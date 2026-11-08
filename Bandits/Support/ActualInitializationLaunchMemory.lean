/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualReferenceInitializationHorizon

/-!
# Original initialization proposal-memory provenance

Sources: `sources/zip4/manuscript/07_public_setup.tex:93-114,121-164`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,376-423`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

Internal deterministic results on the explicit no-initialization-failure and
no-virtual-false-forward domain. The memory invariant projects only ordinary
proposal memory. It starts at the actual all-bootstrap carry, is installed by
actual first declarations, and is preserved by the accepted physical fold and
boundary constructors. All ordinary buffers and decoder banks remain intact.
No unconditional corrected launch, conditional law, or source closure is claimed.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualReferenceInitializationHorizon

namespace Bandits.Support.ActualInitializationLaunchMemory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- Only the memory projection of each declared ordinary follower is constrained.
Bootstrap numerators, rows, activations, ordinary registers, and dagger are not
constrained by this predicate. -/
def initial_memories (followers : Fin (p.m - 1) → FollowerCarry p rate) : Prop :=
  ∀ i row activation state memory,
    followers i = .declared row activation (.ordinary state memory) →
      memory = ActiveFollowerLifecycle.initialMemory p

/-- The actual source base has no declared follower. -/
theorem initialCarry_initial_memories (C_star C_h : ℝ) :
    initial_memories (initialCarry p rate C_star C_h).followers := by
  intro i row activation state memory h
  cases h

/-- Local preservation from an honest incoming prefix and the literal generated
DOWN exclusion. The incoming memory invariant is an induction input here only;
the source-root results below initialize and discharge it. -/
theorem foldBlock_ordinary_memory
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hmem : initial_memories actual.followers)
    (i : Fin (p.m - 1)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : (foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards actual).followers i = .declared row activation (.ordinary state memory)) :
    memory = ActiveFollowerLifecycle.initialMemory p := by
  obtain ⟨_, _, _, hmemory⟩ := ActualReferenceInitializationFold.foldBlock_related
    source rewards rate C_star C_h b h actual past hr hdown
  have hm := hmemory i
  change ActualReferenceInitializationFold.followerMemory rate _
      ((foldBlock p rate _ source rewards actual).followers i) =
    ActualReferenceInitializationFold.followerMemory rate _
      (beginFollowerBlock p rate _ source i (actual.followers i)) at hm
  rw [hout] at hm
  cases hf : actual.followers i with
  | bootstrap numerators lowerBound =>
      rw [hf] at hm
      cases hm
  | declared oldRow oldActivation configuration =>
      cases configuration with
      | dagger =>
          rw [hf] at hm
          cases hm
      | ordinary oldState oldMemory =>
          rw [hf] at hm
          exact (Option.some.inj hm).trans
            (hmem i oldRow oldActivation oldState oldMemory hf)

/-- A boundary preserves an ordinary memory exactly; only the bootstrap first
declaration constructor creates initial memory. No ordinary state is reset. -/
theorem boundary_initial_memories
    (block : Fin (n_boot p))
    (followers : Fin (p.m - 1) → ActualInitializationPhysicalStep.FollowerState p rate block)
    (hmem : ∀ i row activation state memory,
      followers i = .declared row activation (.ordinary state memory) →
        memory = ActiveFollowerLifecycle.initialMemory p) :
    initial_memories (fun i => followerCarryAtBlockBoundary p rate block (followers i)) := by
  intro i row activation state memory hout
  cases hf : followers i with
  | bootstrap startup =>
      cases hpending : BootstrapObservedFollower.pendingDeclaration startup.blockCase with
      | none =>
          simp only [followerCarryAtBlockBoundary, boundaryOutputFromFollower, hf,
            hpending, Option.elim_none, followerCarryOfBoundaryOutput] at hout
          cases hout
      | some saved =>
          simp only [followerCarryAtBlockBoundary, boundaryOutputFromFollower, hf,
            hpending, Option.elim_some, followerCarryOfBoundaryOutput] at hout
          cases hout
          rfl
  | declared oldRow oldActivation configuration =>
      cases configuration with
      | dagger =>
          simp only [followerCarryAtBlockBoundary, boundaryOutputFromFollower, hf,
            followerCarryOfBoundaryOutput] at hout
          cases hout
      | ordinary oldState oldMemory =>
          have heq : FollowerCarry.declared oldRow oldActivation (.ordinary oldState oldMemory) =
              (FollowerCarry.declared row activation (.ordinary state memory) : FollowerCarry p rate) :=
            by simpa only [hf, followerCarryAtBlockBoundary, boundaryOutputFromFollower,
              followerCarryOfBoundaryOutput] using hout
          cases heq
          exact hmem i row activation state memory hf

private theorem combinedBoundaryHandoff_followers
    {block : Fin (n_boot p)} {source : SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p} {C_star C_h : ℝ}
    (folded : BlockFoldOutput p rate block source rewards C_star C_h 0) (i : Fin (p.m - 1)) :
    followerCarryOfBoundaryOutput rate
      ((combinedBoundaryHandoff p rate block source rewards C_star C_h folded).followers i) =
      followerCarryAtBlockBoundary p rate block (folded.followers i) := by
  rfl

-- Explicit equations for the dependent disposition eliminator in the existing
-- runFrom definition. These are ordinary equality elimination, not a new run.
private theorem disposition_cases_continueNext
    {block : Fin (n_boot p)} {α : Type}
    {d : BoundaryDisposition p rate block}
    {onContinue : ∀ next nextCarry, d = .continueNext next nextCarry → α}
    {onLaunch : ∀ launch seed, d = .launched launch seed → α}
    {onExhaust : ∀ live, d = .exhausted live → α}
    {next : Fin (n_boot p)} {nextCarry : BlockCarry p rate next}
    (h : d = .continueNext next nextCarry) :
    BoundaryDisposition.casesOn (motive := fun t => d = t → α)
      d onContinue onLaunch onExhaust rfl = onContinue next nextCarry h := by
  cases h
  rfl

private theorem disposition_cases_launched
    {block : Fin (n_boot p)} {α : Type}
    {d : BoundaryDisposition p rate block}
    {onContinue : ∀ next nextCarry, d = .continueNext next nextCarry → α}
    {onLaunch : ∀ launch seed, d = .launched launch seed → α}
    {onExhaust : ∀ live, d = .exhausted live → α}
    {launch : BootstrapCoordinatorLocalRound.LaunchedBlock p}
    {seed : CoordinatorLearnerZeroSeed p} (h : d = .launched launch seed) :
    BoundaryDisposition.casesOn (motive := fun t => d = t → α)
      d onContinue onLaunch onExhaust rfl = onLaunch launch seed h := by
  cases h
  rfl

private theorem disposition_cases_exhausted
    {block : Fin (n_boot p)} {α : Type}
    {d : BoundaryDisposition p rate block}
    {onContinue : ∀ next nextCarry, d = .continueNext next nextCarry → α}
    {onLaunch : ∀ launch seed, d = .launched launch seed → α}
    {onExhaust : ∀ live, d = .exhausted live → α}
    {live : BootstrapCoordinatorLocalRound.PrelaunchBlock p} (h : d = .exhausted live) :
    BoundaryDisposition.casesOn (motive := fun t => d = t → α)
      d onContinue onLaunch onExhaust rfl = onExhaust live h := by
  cases h
  rfl

private theorem apply_ndrec_eq {ι α : Type} {d a b : ι}
    (f : d = a → α) (h : a = b) (e : d = b) :
    (Eq.ndrec (motive := fun t => d = t → α) f h) e = f (e.trans h.symm) := by
  cases h
  rfl

/-- Memory induction over the actual dependent recursion. Reference relations
are obtained at each successor from the accepted one-block comparison; this
proof adds only the memory projection. Its arbitrary incoming invariant is
initialized by the source constructor in the root theorem. -/
private theorem runFrom_initial_memories
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (block : Fin (n_boot p)) (carry : BlockCarry p rate block)
    (past : List (PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate block carry
      (ReferenceInitializationRun.run (referenceInput source rewards C_star C_h rate) block.val) past)
    (hmem : initial_memories carry.followers) :
    let suffix := runFrom p rate source rewards block carry
    (∀ execution ∈ suffix.continuedBlocks,
      initial_memories execution.carry.followers ∧ initial_memories execution.nextCarry.followers) ∧
    initial_memories (fun i => followerCarryOfBoundaryOutput rate (suffix.terminalHandoff.followers i)) ∧
    ∃ actual : BlockCarry p rate suffix.terminalBlock,
      initial_memories actual.followers ∧
      actual.C_star = suffix.terminalC_star ∧ actual.C_h = suffix.terminalC_h ∧
      HEq suffix.terminalFold (foldBlock p rate suffix.terminalBlock source rewards actual) := by
  dsimp only
  let x := referenceInput source rewards C_star C_h rate
  generalize hb : ReferenceInitializationRun.run x block.val = b at hr
  have h : b.completed < n_boot p := by rw [hr.1]; exact block.isLt
  have hs : block = ReferenceInitializationRun.nextBlock b h := Fin.ext hr.1.symm
  have hcross : (ReferenceInitializationRun.run x block.val).crossing = none := by
    rw [hb]; exact hr.2.1
  have hcompleted : (ReferenceInitializationRun.run x block.val).completed < n_boot p := by
    rw [hb]; exact h
  have hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown x b h i := by
    cases hb
    exact generatedBlockDown_false_of_no_initialization_failure x hinit
      block.val block.isLt hcross hcompleted
  have hclean : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical x b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix (ReferenceInitializationRun.physical x b h)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T := by
    cases hb
    exact cleanPrefix_of_no_actual_false_forward source rewards C_star C_h rate hfalse
      block.val block.isLt hcross hcompleted
  have hfoldMem : ∀ i row activation state memory,
      (foldBlock p rate block source rewards carry).followers i =
        .declared row activation (.ordinary state memory) →
      memory = ActiveFollowerLifecycle.initialMemory p := by
    cases hs
    exact foldBlock_ordinary_memory source rewards C_star C_h b h carry past hr hdown hmem
  have hboundary := boundary_initial_memories block
    (foldBlock p rate block source rewards carry).followers hfoldMem
  let folded := foldBlock p rate block source rewards carry
  let handoff := combinedBoundaryHandoff p rate block source rewards carry.C_star carry.C_h folded
  have hhandoff : initial_memories
      (fun i => followerCarryOfBoundaryOutput rate (handoff.followers i)) := by
    simpa only [handoff, combinedBoundaryHandoff_followers] using hboundary
  cases hd : handoff.disposition with
  | continueNext next nextCarry =>
      have hcontinue : (combinedBoundaryHandoff p rate block source rewards
          carry.C_star carry.C_h folded).disposition = .continueNext next nextCarry := hd
      obtain ⟨hnext, _, _, live, _, _, _, hfollowers⟩ :=
        combinedBoundaryHandoff_continueNext_facts folded next nextCarry hcontinue
      have hnextMem : initial_memories nextCarry.followers := by
        intro i row activation state memory heq
        rw [hfollowers i] at heq
        exact hboundary i row activation state memory heq
      have hrelated : BlockStartRelated source rewards C_star C_h rate next nextCarry
          (ReferenceInitializationRun.finishBlock x b h) (past ++ folded.records) := by
        have localContinue := hcontinue
        cases hs
        exact (ActualReferenceInitializationBoundary.combinedBoundaryHandoff_continueNext_related
          source rewards rate C_star C_h b h carry past hr hdown hclean
          next nextCarry localContinue).2
      have hfinish : ReferenceInitializationRun.run x next.val =
          ReferenceInitializationRun.finishBlock x b h := by
        rw [hnext, ReferenceInitializationRun.run_succ, hb]
        exact ReferenceInitializationRun.advance_of_no_crossing x b hr.2.1 h
      rw [← hfinish] at hrelated
      have htail := runFrom_initial_memories p rate source rewards C_star C_h hinit hfalse
        next nextCarry (past ++ folded.records) hrelated hnextMem
      rw [runFrom.eq_1, disposition_cases_continueNext hcontinue, apply_ndrec_eq]
      refine ⟨?_, htail.2⟩
      intro execution he
      rcases List.mem_cons.mp he with he | he
      · cases he
        exact ⟨hmem, hnextMem⟩
      · exact htail.1 execution he
  | launched launch seed =>
      have hlaunch : (combinedBoundaryHandoff p rate block source rewards
          carry.C_star carry.C_h folded).disposition = .launched launch seed := hd
      rw [runFrom.eq_1, disposition_cases_launched hlaunch, apply_ndrec_eq]
      refine ⟨?_, hhandoff, carry, hmem, rfl, rfl, HEq.rfl⟩
      intro execution he
      exact (List.not_mem_nil he).elim
  | exhausted live =>
      have hexhaust : (combinedBoundaryHandoff p rate block source rewards
          carry.C_star carry.C_h folded).disposition = .exhausted live := hd
      rw [runFrom.eq_1, disposition_cases_exhausted hexhaust, apply_ndrec_eq]
      refine ⟨?_, hhandoff, carry, hmem, rfl, rfl, HEq.rfl⟩
      intro execution he
      exact (List.not_mem_nil he).elim
termination_by n_boot p - block.val
decreasing_by omega

/-- All prior declarations, the terminal incoming carry, and the terminal
handoff in the original source run have initial proposal memory. This covers
both honest exhaustion and launch, including launch after the final block.
The two event complements are explicit internal domain restrictions. -/
theorem source_declared_memory_initial
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source)) :
    let result := sourceInitializedRun p rate source rewards C_star C_h
    (∀ execution ∈ result.continuedBlocks,
      initial_memories execution.carry.followers ∧ initial_memories execution.nextCarry.followers) ∧
    initial_memories (fun i => followerCarryOfBoundaryOutput rate (result.terminalHandoff.followers i)) ∧
    ∃ actual : BlockCarry p rate result.terminalBlock,
      initial_memories actual.followers ∧
      actual.C_star = result.terminalC_star ∧ actual.C_h = result.terminalC_h ∧
      HEq result.terminalFold (foldBlock p rate result.terminalBlock source rewards actual) := by
  have hr := initial_related source rewards C_star C_h rate
  have hrRun : BlockStartRelated source rewards C_star C_h rate (firstBlock p)
      (initialCarry p rate C_star C_h)
      (ReferenceInitializationRun.run (referenceInput source rewards C_star C_h rate)
        (firstBlock p).val) [] := by
    simpa only [firstBlock, ReferenceInitializationRun.run_zero] using hr
  exact runFrom_initial_memories p rate source rewards C_star C_h hinit hfalse
    (firstBlock p) (initialCarry p rate C_star C_h) [] hrRun
    (initialCarry_initial_memories C_star C_h)

/-- The existing source launch witness, now characterized using memory derived
from the entire original initialization recursion. Activations are the generated
`some` values; the explicit Option projection retains the `T + 1` sentinel in
its absent case without constructing a new activation or launch map. -/
theorem source_launched_state_characterization
    (p : Parameters) (rate : RateInput p) (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : CoordinatorLearnerZeroSeed p)
    (hlaunched : (sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
      .launched launch seed) :
    let x := referenceInput source rewards C_star C_h rate
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let result := sourceInitializedRun p rate source rewards C_star C_h
    ∃ actual : BlockCarry p rate result.terminalBlock,
      BlockStartRelated source rewards C_star C_h rate result.terminalBlock actual
        (ReferenceInitializationRun.run x result.terminalBlock.val)
        (result.records.take (BootstrapObservedFollower.blockStart p result.terminalBlock)) ∧
      actual.C_star = C_star ∧ actual.C_h = C_h ∧
      actual.C_star = result.terminalC_star ∧ actual.C_h = result.terminalC_h ∧
      initial_memories actual.followers ∧
      HEq result.terminalFold (foldBlock p rate result.terminalBlock source rewards actual) ∧
      ∃ active : ReferenceActivePhysicalStep.State p rate,
        active.coordinator = .first ∧
        active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
        (∀ i, followerCarryOfBoundaryOutput rate (result.terminalHandoff.followers i) =
          .declared J (active.activations i) (active.followers i)) ∧
        (∀ i, follower_start_related x source rate rfl (ReferenceInitializationRun.output x) i
          (.declared J (active.activations i) (active.followers i))) ∧
        (∀ i, active.followers i = .ordinary
          (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) (refFollower i))
          (ActiveFollowerLifecycle.initialMemory p)) ∧
        (∀ i, (ReferenceInitializationRun.output x).activation (refFollower i) =
          some (active.activations i)) ∧
        (∀ i, (active.activations i).val =
          match (ReferenceInitializationRun.output x).activation (refFollower i) with
          | none => p.T + 1
          | some activation => activation.val) ∧
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
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  let result := sourceInitializedRun p rate source rewards C_star C_h
  obtain ⟨actual, hr, hfold, active, hcoord, hup, hcarry, hrelated, hregisters,
      hbound, htime, hpreserved⟩ :=
    ActualReferenceInitializationHorizon.sourceInitializedRun_launched_state
      p rate source rewards C_star C_h hinit hfalse launch seed hlaunched
  have hmemory := (source_declared_memory_initial p rate source rewards C_star C_h hinit hfalse).2.1
  have hconfiguration : ∀ i, active.followers i = .ordinary
      (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) (refFollower i))
      (ActiveFollowerLifecycle.initialMemory p) := by
    intro i
    obtain ⟨state, memory, hf, hstate, _⟩ := hregisters i
    have hm : memory = ActiveFollowerLifecycle.initialMemory p :=
      hmemory i J (active.activations i) state memory (by simpa only [hf] using hcarry i)
    rw [hf, hstate, hm]
  have hactivation : ∀ i, (ReferenceInitializationRun.output x).activation (refFollower i) =
      some (active.activations i) := by
    intro i
    have hi := hrelated i
    rw [hconfiguration i] at hi
    exact hi.2.1
  have hincoming : initial_memories actual.followers := by
    intro i row activation state memory hf
    have heq := (hpreserved i row activation state memory hf).2
    rw [hconfiguration i] at heq
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj heq).2.symm
  have hconstants := sourceInitializedRun_shared_constants p rate source rewards C_star C_h
  refine ⟨actual, hr, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
    hr.2.2.2.2.1.trans hconstants.1.symm, hr.2.2.2.2.2.1.trans hconstants.2.symm,
    hincoming, hfold, active, hcoord, hup, hcarry, hrelated, hconfiguration,
    hactivation, ?_, hregisters, hbound, htime, hpreserved⟩
  intro i
  rw [hactivation i]

end Bandits.Support.ActualInitializationLaunchMemory

end
