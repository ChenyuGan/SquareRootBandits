/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix
import Lean.Elab.Tactic.Omega

/-!
# Actual prelaunch DOWN decision readouts

The definitions here read the ordinary decision made by the actual generated
prelaunch prefix. They do not introduce another execution or a probabilistic
claim. Source ranges: `07_public_setup.tex:127-164`,
`05_binary_transport.tex:7-55`, and
`appendix_a_local_protocol.tex:92-157`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferencePrelaunchDownDecisionReadout

open ConstructorDimensions
open BootstrapDimensions
open ReferenceGeneratedPrelaunchDownPrefix
open ReferencePrelaunchFollower
open ReferenceInitializationRun
open AffineBatchDecoder
open OrdinaryMessageCodec
open scoped Classical

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)

/-- The ordinary prelaunch DOWN failure bit at the current physical round.
Only an active branch makes the actual ordinary call; inactive and stopped
branches therefore read false. -/
def prelaunchDownFailureAt (i : Fin (p.m - 1)) (r : Fin p.T) : Bool := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  exact match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | .inl (.inl active) =>
      decide (passing_at rate.eta i x.row
        active.val.2.1 r
        (ownEntry
          (physical x active.val.1.val
            active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r)
        active.val.2.2.2.downBatch)
  | .inl (.inr _) => false
  | .inr _ => false

/-- The strict-past decoder flag includes every detected round below `n` and
uses the actual source event at its original calendar date. -/
def prelaunchPastDecoderFlag (n : ℕ) (hn : n ≤ p.T) : Bool :=
  decide (∃ j : Fin n, ∃ i : Fin (p.m - 1),
    prelaunchDownFailureAt rate rewards C_star C_h z i (Fin.castLE hn j) = true)

/-- The Boolean readout is exactly the current ordinary parsed acceptance on
an active prefix, and is false on the other actual selector branches. -/
theorem prelaunchDownFailureAt_true_iff
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    prelaunchDownFailureAt rate rewards C_star C_h z i r = true ↔
      ∃ active : ActiveProjection p i r.val
          (sourceReferenceInput rate rewards C_star C_h z).row
          (Nat.le_of_lt r.isLt)
          (sourceReferenceInput rate rewards C_star C_h z)
          (roundBlockIndex p r),
        source_prelaunch_down_prefix rate rewards C_star C_h z i r =
            .inl (.inl active) ∧
        passing_at rate.eta i
          (sourceReferenceInput rate rewards C_star C_h z).row
          active.val.2.1 r
          (ownEntry
            (physical
              (sourceReferenceInput rate rewards C_star C_h z)
              active.val.1.val active.val.1.property.1)
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r)
          active.val.2.2.2.downBatch := by
  classical
  unfold prelaunchDownFailureAt
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active => simp
      | inr inactive => simp
  | inr stopped => simp

/-- The actual ordinary replay has zero accepted start and no assignment
effects, even when an earlier parse passed and was suppressed. -/
theorem prelaunch_active_registers (i : Fin (p.m - 1)) (r : Fin p.T)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r)) :
    active.val.2.2.2.lastDown = none ∧ acceptedStart active.val.2.2.2 = 0 ∧
    active.val.2.2.2.S = 0 ∧ active.val.2.2.2.delta = 0 ∧
    active.val.2.2.2.backlog = 0 ∧ active.val.2.2.2.status = .unoccupied := by
  rw [active.property.choose_spec.2.1]
  exact replay_registers rate.eta i
    (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 active.val.2.2.1
    (Nat.le_of_lt r.isLt)

/-- A passing current parse comes from the exact currently completed batch.
The output includes the raw solution, all equations, uniqueness, the exact
DOWN parser equation and ordinary accepted-start/calendar-time test. -/
theorem prelaunchDownFailureAt_completedBatch
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (hd : prelaunchDownFailureAt rate rewards C_star C_h z i r = true) :
    ∃ active : ActiveProjection p i r.val
        (sourceReferenceInput rate rewards C_star C_h z).row
        (Nat.le_of_lt r.isLt)
        (sourceReferenceInput rate rewards C_star C_h z)
        (roundBlockIndex p r),
    source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inl (.inl active) ∧
    ∃ w : AffineChannelLaw.Word (width p),
    ∃ M : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta),
      let own := ownEntry
        (physical
          (sourceReferenceInput rate rewards C_star C_h z)
          active.val.1.val active.val.1.property.1)
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) r
      let bank := active.val.2.2.2.downBatch
      let B := bank.pending ++ positiveAt p
        (traceAt i
          (sourceReferenceInput rate rewards C_star C_h z).row
          active.val.2.1 r own) r
      (decodeAt i
        (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r own bank).2 = some w ∧
      B.length = quota p ∧
      batchOutput B = some w ∧
      satisfies (samples B) w ∧
      (∀ v, satisfies (samples B) v → v = w) ∧
      OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
        (some ((OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w)) = some M ∧
      (OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w =
          OrdinaryMessageCodec.encodeDown
            (ReferencePrelaunchFollower.codecParams p rate.eta) M ∧
      OrdinaryMessageCodec.acceptDown
        (ReferencePrelaunchFollower.codecParams p rate.eta) 0 (r.val + 1) M := by
  classical
  obtain ⟨active, hpref, hpass⟩ :=
    (prelaunchDownFailureAt_true_iff rate rewards C_star C_h z i r).mp hd
  rcases hpass with ⟨M, hparsed, haccept⟩
  let own := ownEntry
    (physical
      (sourceReferenceInput rate rewards C_star C_h z)
      active.val.1.val active.val.1.property.1)
    (PublicDiscreteDraws.followerPlayer p.two_le_m
      (ActualReferenceInitializationBlock.refFollower i)) r
  let bank := active.val.2.2.2.downBatch
  let B := bank.pending ++ positiveAt p
    (traceAt i
      (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r own) r
  have hcensus := source_prelaunch_down_prefix_census rate rewards C_star C_h z i r
  rw [hpref] at hcensus
  dsimp only at hcensus
  rcases hcensus with ⟨_, _, _, hshort⟩
  change bank.pending.length < quota p at hshort
  have hparsed' : parsedAt rate.eta i
      (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r own bank = some M := hparsed
  obtain ⟨w, hraw, hge, hbatch, hencode⟩ :=
    parsedAt_some_completed rate.eta i
      (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r own bank M hparsed'
  have hposlen : (positiveAt p
      (traceAt i
        (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r own) r).length ≤ 1 := by
    unfold positiveAt
    split <;> simp
  have hlower : quota p ≤ bank.pending.length +
      (positiveAt p
        (traceAt i
          (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r own) r).length := by
    simpa only [B, bank, List.length_append] using hge
  have hlen : B.length = quota p := by
    dsimp only [B]
    rw [List.length_append]
    omega
  have hsolution := (batchOutput_eq_some_iff B w).mp hbatch
  have hsat : satisfies (samples B) w :=
    (satisfies_samples_iff B w).2 hsolution.1
  have huniq : ∀ v, satisfies (samples B) v → v = w := by
    intro v hv
    exact hsolution.2 v ((satisfies_samples_iff B v).1 hv)
  have hparse : OrdinaryMessageCodec.parseDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (some ((OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w)) = some M := by
    change OrdinaryMessageCodec.parseDown
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      ((decodeAt i
        (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r own bank).2.map
        (OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta)).symm) = some M at hparsed'
    rw [hraw] at hparsed'
    exact hparsed'
  exact ⟨active, hpref, w, M, hraw, hlen, hbatch, hsat, huniq, hparse, hencode, haccept⟩

/-- The current readout is exactly the actual quota completion, unique raw
solution, exact DOWN parse and ordinary accepted-start/calendar test. -/
theorem prelaunchDownFailureAt_completedBatch_iff
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    prelaunchDownFailureAt rate rewards C_star C_h z i r = true ↔
      ∃ active : ActiveProjection p i r.val
          (sourceReferenceInput rate rewards C_star C_h z).row
          (Nat.le_of_lt r.isLt)
          (sourceReferenceInput rate rewards C_star C_h z)
          (roundBlockIndex p r),
      source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inl (.inl active) ∧
      ∃ w : AffineChannelLaw.Word (width p),
      ∃ M : OrdinaryMessageCodec.DownRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta),
        let own := ownEntry
          (physical
            (sourceReferenceInput rate rewards C_star C_h z)
            active.val.1.val active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r
        let bank := active.val.2.2.2.downBatch
        let B := bank.pending ++ positiveAt p
          (traceAt i
            (sourceReferenceInput rate rewards C_star C_h z).row
            active.val.2.1 r own) r
        (decodeAt i
          (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r own bank).2 = some w ∧
        B.length = quota p ∧
        batchOutput B = some w ∧
        satisfies (samples B) w ∧
        (∀ v, satisfies (samples B) v → v = w) ∧
        OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
          (some ((OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w)) = some M ∧
        (OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta)).symm w =
            OrdinaryMessageCodec.encodeDown
              (ReferencePrelaunchFollower.codecParams p rate.eta) M ∧
        OrdinaryMessageCodec.acceptDown
          (ReferencePrelaunchFollower.codecParams p rate.eta) 0 (r.val + 1) M := by
  constructor
  · exact prelaunchDownFailureAt_completedBatch rate rewards C_star C_h z i r
  · rintro ⟨active, hpref, w, M, hraw, _hlen, _hbatch, _hsat, _huniq,
      hparse, _hencode, haccept⟩
    apply (prelaunchDownFailureAt_true_iff rate rewards C_star C_h z i r).mpr
    refine ⟨active, hpref, M, ?_, haccept⟩
    unfold parsedAt
    rw [hraw]
    exact hparse

/-- The selector's state immediately before `r` is the generated physical
block fold immediately before the same offset. The prefix/suffix decomposition
is an actual `blockIndices` decomposition; no new event is assumed. -/
private theorem activePrefixState_blockBefore (i : Fin (p.m - 1)) (r : Fin p.T)
    (active : ActiveProjection p i r.val (sourceReferenceInput rate rewards C_star C_h z).row
      (Nat.le_of_lt r.isLt) (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (ha : active.val.1.val.activation
      (ActualReferenceInitializationBlock.refFollower i) = some active.val.2.1)
    (before : List (Fin (ReferencePrelaunchPhysicalReplay.blockEnd p (nextBlock active.val.1.val
        active.val.1.property.1)))) (u : Fin (ReferencePrelaunchPhysicalReplay.blockEnd p
      (nextBlock active.val.1.val active.val.1.property.1)))
    (after : List (Fin (ReferencePrelaunchPhysicalReplay.blockEnd p (nextBlock active.val.1.val
        active.val.1.property.1)))) (hlist : ReferencePrelaunchPhysicalReplay.blockIndices
      (replayInput (sourceReferenceInput rate rewards C_star C_h z)
        active.val.1.val active.val.1.property.1
        (ActualReferenceInitializationBlock.refFollower i) active.val.2.1 ha) =
          before ++ u :: after) (htime : calendar (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
        (nextBlock active.val.1.val active.val.1.property.1)) u = r) :
    active.val.2.2.2 = ReferencePrelaunchFollower.run (BootstrapPhysicalInput.sourceFollowerIndex p
        (ActualReferenceInitializationBlock.refFollower i))
      (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1
      (ReferencePrelaunchPhysicalReplay.chronologicalHistory (replayInput
          (sourceReferenceInput rate rewards C_star C_h z) active.val.1.val active.val.1.property.1
          (ActualReferenceInitializationBlock.refFollower i) active.val.2.1 ha))
      (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p (nextBlock active.val.1.val
          active.val.1.property.1)) before (ordinary
        (sourceReferenceInput rate rewards C_star C_h z) active.val.1.val
        (ActualReferenceInitializationBlock.refFollower i)) ∧
    ReferencePrelaunchPhysicalReplay.chronologicalHistory (replayInput
        (sourceReferenceInput rate rewards C_star C_h z) active.val.1.val active.val.1.property.1
        (ActualReferenceInitializationBlock.refFollower i) active.val.2.1 ha) u = ownEntry (physical
          (sourceReferenceInput rate rewards C_star C_h z) active.val.1.val active.val.1.property.1)
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) r := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let f := ActualReferenceInitializationBlock.refFollower i
  let b := active.val.1.val
  let h := active.val.1.property.1
  let a := active.val.2.1
  let block := replayInput x b h f a ha
  let hist := ReferencePrelaunchPhysicalReplay.chronologicalHistory block
  let hEnd := ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
    (nextBlock b h)
  rcases active.property with ⟨hbefore, hactivation, hstate, hhistory⟩
  have hboundary : b = ReferenceInitializationRun.run x (roundBlockIndex p r).val :=
    active.val.1.property.2.2
  have hcross : b.crossing = none := active.val.1.property.2.1
  have hcrossRun : (ReferenceInitializationRun.run x (roundBlockIndex p r).val).crossing = none := by
    rw [← hboundary]
    exact hcross
  have hnotForced : b.forcedFailure f = false := by
    rw [hboundary]
    exact run_no_forced_before_launch x
      (roundBlockIndex p r).val hcrossRun f
  have hrunEnd : r.val ≤ elapsed p (b.completed + 1) :=
    hbefore
  have hR : r.val ≤ ReferencePrelaunchPhysicalReplay.blockEnd p
      (nextBlock b h) := by
    rw [← elapsed_succ_eq_blockEnd b h]
    exact hrunEnd
  have hHistBlock : hist = extendedHistory x b h
      (PublicDiscreteDraws.followerPlayer p.two_le_m f) :=
    replayInput_history x b h f a ha
  have hidx : BootstrapPhysicalInput.sourceFollowerIndex p f = i := by
    apply Fin.ext
    rfl
  have huMem : u ∈ ReferencePrelaunchPhysicalReplay.blockIndices block := by
    rw [hlist]
    simp
  have huBounds := InitializationFailureProvenance.blockIndices_member_bounds block huMem
  have htimeVal : u.val = r.val := congrArg Fin.val htime
  have hroundBounds :
      ReferencePrelaunchPhysicalReplay.blockStart p
          (nextBlock b h) ≤ r.val ∧
      r.val < ReferencePrelaunchPhysicalReplay.blockEnd p
          (nextBlock b h) := by
    constructor <;> omega
  have hbeforeLenLt : before.length <
      ReferencePrelaunchPhysicalReplay.blockLength p
        (nextBlock b h) := by
    have hlen : ReferencePrelaunchPhysicalReplay.blockLength p
        (nextBlock b h) =
          before.length + (after.length + 1) := by
      simpa only [ReferencePrelaunchPhysicalReplay.blockIndices_length,
        List.length_append, List.length_cons] using congrArg List.length hlist
    omega
  have hbeforeLenList : before.length <
      (ReferencePrelaunchPhysicalReplay.blockIndices block).length := by
    rw [ReferencePrelaunchPhysicalReplay.blockIndices_length]
    exact hbeforeLenLt
  have hget? : (ReferencePrelaunchPhysicalReplay.blockIndices block)[before.length]? = some u := by
    rw [hlist]
    simp
  have hget : (ReferencePrelaunchPhysicalReplay.blockIndices block)[before.length]'hbeforeLenList = u := by
    have h := hget?
    rw [List.getElem?_eq_getElem hbeforeLenList] at h
    exact Option.some.inj h
  have hgetBlock : (ReferencePrelaunchPhysicalReplay.blockIndices block)[before.length]'hbeforeLenList =
      ReferencePrelaunchPhysicalReplay.blockEmbed
        (⟨before.length, hbeforeLenLt⟩ : Fin
          (ReferencePrelaunchPhysicalReplay.blockLength p
            (nextBlock b h))) := by
    simp only [ReferencePrelaunchPhysicalReplay.blockIndices,
      List.getElem_map, List.getElem_ofFn]
  have hbeforeVal : ReferencePrelaunchPhysicalReplay.blockStart p (nextBlock b h) +
      before.length = r.val := by
    have hv := congrArg Fin.val (hget.symm.trans hgetBlock)
    simp only [ReferencePrelaunchPhysicalReplay.blockEmbed] at hv
    omega
  have hbeforeTake : before =
      (ReferencePrelaunchPhysicalReplay.blockIndices block).take before.length := by
    rw [hlist]
    simp only [List.take_left]
  have hprefixIndices :
      (List.ofFn (fun q : Fin r.val => Fin.castLE hR q)) =
        ReferencePrelaunchPhysicalReplay.prefixIndices block ++ before := by
    have hcastTake' :
        (List.ofFn (fun q : Fin r.val => Fin.castLE hR q)) =
          (List.ofFn (fun q : Fin
            (ReferencePrelaunchPhysicalReplay.blockEnd p
              (nextBlock b h)) => q)).take r.val := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_take]
        rw [Nat.min_eq_left hR]
      · intro j hj hj'
        simp only [List.getElem_ofFn, List.getElem_take]
        apply Fin.ext
        rfl
    calc
      (List.ofFn (fun q : Fin r.val => Fin.castLE hR q)) =
          (List.ofFn (fun q : Fin
            (ReferencePrelaunchPhysicalReplay.blockEnd p
              (nextBlock b h)) => q)).take r.val := hcastTake'
      _ = (ReferencePrelaunchPhysicalReplay.prefixIndices block ++
          ReferencePrelaunchPhysicalReplay.blockIndices block).take r.val := by
        rw [replay_indices block]
      _ = ReferencePrelaunchPhysicalReplay.prefixIndices block ++
          (ReferencePrelaunchPhysicalReplay.blockIndices block).take before.length := by
        rw [List.take_append, ReferencePrelaunchPhysicalReplay.prefixIndices_length]
        have hstart : (ReferencePrelaunchPhysicalReplay.prefixIndices block).length ≤ r.val := by
          rw [ReferencePrelaunchPhysicalReplay.prefixIndices_length]
          exact hroundBounds.1
        rw [List.take_of_length_le hstart]
        rw [show r.val - ReferencePrelaunchPhysicalReplay.blockStart p
          (nextBlock b h) = before.length by omega]
      _ = ReferencePrelaunchPhysicalReplay.prefixIndices block ++ before :=
        congrArg (ReferencePrelaunchPhysicalReplay.prefixIndices block ++ ·) hbeforeTake.symm
  have hRunArgument (q : Fin r.val) :
      calendar (Nat.le_of_lt r.isLt) q =
        calendar hEnd (Fin.castLE hR q) := by
    apply Fin.ext
    rfl
  have hHistoryArgument (q : Fin r.val) : active.val.2.2.1 q = hist (Fin.castLE hR q) := by
    rw [hhistory]
    dsimp only [ReferencePrelaunchLifecycleReplay.prefixHistory]
    rw [← hHistBlock]
    congr 1
  have hRunMap (us : List (Fin r.val))
      (st : ReferencePrelaunchFollower.State p x.eta) :
      ReferencePrelaunchFollower.run
          (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a active.val.2.2.1
          (Nat.le_of_lt r.isLt) us st =
        ReferencePrelaunchFollower.run
          (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a hist hEnd
          (us.map (Fin.castLE hR)) st := by
    induction us generalizing st with
    | nil => rfl
    | cons q us ih =>
        simp only [ReferencePrelaunchFollower.run, List.map_cons]
        rw [hRunArgument q, hHistoryArgument q, ih]
  have hcastMap : (List.ofFn (fun q : Fin r.val => q)).map (Fin.castLE hR) =
      List.ofFn (fun q : Fin r.val => Fin.castLE hR q) := List.map_ofFn
  have hprefixRun : ReferencePrelaunchFollower.run
      (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a hist hEnd
      (ReferencePrelaunchPhysicalReplay.prefixIndices block)
      (ReferencePrelaunchFollower.initial p x.eta) =
        ReferencePrelaunchPhysicalReplay.incomingState block := by
    change ReferencePrelaunchFollower.run
        (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a hist hEnd
        ((List.ofFn (fun q : Fin
          (ReferencePrelaunchPhysicalReplay.blockStart p
            (nextBlock b h)) => q)).map
          (ReferencePrelaunchPhysicalReplay.prefixEmbed (p := p)
            (s := nextBlock b h)))
        (ReferencePrelaunchFollower.initial p x.eta) = _
    exact ReferencePrelaunchPhysicalReplay.run_prefix_map block
      (List.ofFn (fun q : Fin (ReferencePrelaunchPhysicalReplay.blockStart p
        (nextBlock b h)) => q))
      (ReferencePrelaunchFollower.initial p x.eta)
  have hincoming : ReferencePrelaunchPhysicalReplay.incomingState block =
      ordinary x b f :=
    replayInput_incoming x b h f a ha hnotForced
  have hsourceReplay : active.val.2.2.2 =
      ReferencePrelaunchFollower.run i x.row a active.val.2.2.1
        (Nat.le_of_lt r.isLt) (List.ofFn (fun q : Fin r.val => q))
        (ReferencePrelaunchFollower.initial p x.eta) := by
    rw [hstate]
    rfl
  have hstateOrdinary := hsourceReplay.trans (by
    simpa only [hidx] using hRunMap (List.ofFn (fun q : Fin r.val => q))
      (ReferencePrelaunchFollower.initial p x.eta))
  have hprefixRun' := hprefixRun
  rw [hidx] at hprefixRun'
  rw [hcastMap, hprefixIndices, run_append,
    hprefixRun', hincoming] at hstateOrdinary
  constructor
  · change active.val.2.2.2 = ReferencePrelaunchFollower.run
      (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a hist hEnd before
      (ordinary x b f)
    simpa only [hidx] using hstateOrdinary
  · change hist u = ownEntry (physical x b h)
      (PublicDiscreteDraws.followerPlayer p.two_le_m f) r
    rw [hget.symm.trans hgetBlock, hHistBlock, extendedHistory_block]
    congr 1
    apply Fin.ext
    exact hbeforeVal

private theorem activeDateBlockDecomposition (i : Fin (p.m - 1)) (r : Fin p.T)
    (active : ActiveProjection p i r.val (sourceReferenceInput rate rewards C_star C_h z).row
      (Nat.le_of_lt r.isLt) (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (a : Activation p) (ha : active.val.1.val.activation
      (ActualReferenceInitializationBlock.refFollower i) = some a) : ∃ before u after,
      ReferencePrelaunchPhysicalReplay.blockIndices (replayInput
          (sourceReferenceInput rate rewards C_star C_h z) active.val.1.val active.val.1.property.1
          (ActualReferenceInitializationBlock.refFollower i) a ha) = before ++ u :: after ∧ calendar
        (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p (nextBlock active.val.1.val
            active.val.1.property.1)) u = r := by
  let x := sourceReferenceInput rate rewards C_star C_h z
  let s := roundBlockIndex p r
  let b := active.val.1.val
  let h := active.val.1.property.1
  let f := ActualReferenceInitializationBlock.refFollower i
  have hboundary : b = ReferenceInitializationRun.run x s.val :=
    active.val.1.property.2.2
  have hcross : b.crossing = none := active.val.1.property.2.1
  have hcompleted : b.completed = s.val := by
    have hprogress := run_progress x s.val s.isLt.le
    rcases hprogress with hc | hn
    · rw [← hboundary, hcross] at hc
      cases hc
    · exact (congrArg Boundary.completed hboundary).trans hn
  have hnext : nextBlock b h = s := by
    apply Fin.ext
    simp only [nextBlock, hcompleted]
  have hcalendar : r ∈ BootstrapDimensions.calendarBlock p s :=
    BootstrapDimensions.round_mem_quotient_block p r
  have hcalendar' : r ∈ BootstrapDimensions.calendarBlock p
      (nextBlock b h) := by
    simpa only [hnext] using hcalendar
  obtain ⟨v, hv⟩ := ReferencePrelaunchPhysicalReplay.exists_blockRound p
    (nextBlock b h) r hcalendar'
  let block := replayInput x b h f a ha
  let u := ReferencePrelaunchPhysicalReplay.blockEmbed v
  have htime : calendar
      (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
        (nextBlock b h)) u = r := by
    apply Fin.ext
    simpa only [u, ReferencePrelaunchPhysicalReplay.blockEmbed,
      calendar,
      ReferencePrelaunchPhysicalReplay.blockRound_val] using congrArg Fin.val hv
  have hu : u ∈ ReferencePrelaunchPhysicalReplay.blockIndices block := by
    simp only [u, ReferencePrelaunchPhysicalReplay.blockIndices, List.mem_map]
    exact ⟨v, by simp, rfl⟩
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hu
  refine ⟨(ReferencePrelaunchPhysicalReplay.blockIndices block).take j, u,
    (ReferencePrelaunchPhysicalReplay.blockIndices block).drop (j + 1), ?_, htime⟩
  calc
    ReferencePrelaunchPhysicalReplay.blockIndices block =
        (ReferencePrelaunchPhysicalReplay.blockIndices block).take j ++
          (ReferencePrelaunchPhysicalReplay.blockIndices block).drop j :=
      (List.take_append_drop j (ReferencePrelaunchPhysicalReplay.blockIndices block)).symm
    _ = (ReferencePrelaunchPhysicalReplay.blockIndices block).take j ++
          u :: (ReferencePrelaunchPhysicalReplay.blockIndices block).drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj, hget]

private theorem generatedBlockDecision_mem_transport (x : Input p) (b b' : Boundary p)
    (h : b.completed < n_boot p) (h' : b'.completed < n_boot p)
    (f : ActiveRoundActions.Follower p.m) (a : Activation p)
    (ha : b.activation f = some a) (ha' : b'.activation f = some a)
    (d : Fin p.T × OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p x.eta))
    (hb : b = b') (hd : d ∈ decisions (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a
      (ReferencePrelaunchPhysicalReplay.chronologicalHistory (replayInput x b h f a ha))
      (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p (nextBlock b h))
      (ReferencePrelaunchPhysicalReplay.blockIndices (replayInput x b h f a ha)) (ordinary x b f)) :
    d ∈ decisions (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a
      (ReferencePrelaunchPhysicalReplay.chronologicalHistory (replayInput x b' h' f a ha'))
      (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p (nextBlock b' h'))
      (ReferencePrelaunchPhysicalReplay.blockIndices (replayInput x b' h' f a ha'))
      (ordinary x b' f) := by
  cases hb
  exact hd

/-- A current ordinary DOWN decision is exactly a same-date member of the
generated ordinary replay for the actual processed block. The block witness,
activation, decision and strict physical date are all produced here. -/
theorem prelaunchDownFailureAt_sameDateBlockDecisions (i : Fin (p.m - 1)) (r : Fin p.T) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let f := ActualReferenceInitializationBlock.refFollower i
    prelaunchDownFailureAt rate rewards C_star C_h z i r = true ↔
      ∃ active : ActiveProjection p i r.val x.row (Nat.le_of_lt r.isLt) x (roundBlockIndex p r),
        source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inl (.inl active) ∧
        ∃ a, ∃ ha : active.val.1.val.activation f = some a,
          let b := active.val.1.val
          let block := replayInput x b active.val.1.property.1 f a ha
          ∃ d ∈ decisions (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a
              (ReferencePrelaunchPhysicalReplay.chronologicalHistory block)
              (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p (nextBlock b active.val.1.property.1))
              (ReferencePrelaunchPhysicalReplay.blockIndices block) (ordinary x b f),
            d.1 = r ∧ OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta) 0 (d.1.val + 1) d.2 := by
  classical
  dsimp only
  let x := sourceReferenceInput rate rewards C_star C_h z
  let f := ActualReferenceInitializationBlock.refFollower i
  have hidx : BootstrapPhysicalInput.sourceFollowerIndex p f = i := by
    apply Fin.ext
    rfl
  constructor
  · intro hd
    obtain ⟨active, hpref, M, hparsed, haccept⟩ :=
      (prelaunchDownFailureAt_true_iff rate rewards C_star C_h z i r).mp hd
    let b := active.val.1.val
    let h := active.val.1.property.1
    let a := active.val.2.1
    rcases active.property with ⟨_, ha, _, _⟩
    obtain ⟨before, u, after, hlist, htime⟩ :=
      activeDateBlockDecomposition rate rewards C_star C_h z i r active a ha
    obtain ⟨hstate, hown⟩ := activePrefixState_blockBefore
      rate rewards C_star C_h z i r active ha before u after hlist htime
    refine ⟨active, hpref, a, ha, (r, M), ?_, rfl, haccept⟩
    apply (mem_decisions_iff
      (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a
      (ReferencePrelaunchPhysicalReplay.chronologicalHistory
        (replayInput x b h f a ha))
      (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
        (nextBlock b h))
      (ReferencePrelaunchPhysicalReplay.blockIndices
        (replayInput x b h f a ha))
      (ordinary x b f) (r, M)).mpr
    refine ⟨before, u, after, hlist, htime.symm, ?_⟩
    rw [htime, hown, ← hstate]
    simpa only [hidx, x, a, sourceReferenceInput,
      ActualReferenceInitializationBlock.referenceInput] using hparsed
  · rintro ⟨active, hpref, a, ha, d, hdblock, hdate, haccept⟩
    let b := active.val.1.val
    let h := active.val.1.property.1
    rcases active.property with ⟨_, hactive, _, _⟩
    have hactivation : a = active.val.2.1 := Option.some.inj (ha.symm.trans hactive)
    subst a
    let a := active.val.2.1
    obtain ⟨before, u, after, hlist, htime, hparsed⟩ :=
      (mem_decisions_iff
        (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a
        (ReferencePrelaunchPhysicalReplay.chronologicalHistory
          (replayInput x b h f a ha))
        (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
          (nextBlock b h))
        (ReferencePrelaunchPhysicalReplay.blockIndices
          (replayInput x b h f a ha))
        (ordinary x b f) d).mp hdblock
    have hcal : calendar
        (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
          (nextBlock b h)) u = r := htime.symm.trans hdate
    obtain ⟨hstate, hown⟩ := activePrefixState_blockBefore
      rate rewards C_star C_h z i r active ha before u after hlist hcal
    rw [hcal, hown, ← hstate] at hparsed
    refine (prelaunchDownFailureAt_true_iff rate rewards C_star C_h z i r).mpr
      ⟨active, hpref, d.2, ?_, ?_⟩
    · simpa only [hidx, x, a, sourceReferenceInput,
      ActualReferenceInitializationBlock.referenceInput] using hparsed
    · simpa only [hdate] using haccept

/-- The strict-past source event is exactly an accepted ordinary DOWN decision
in one of the actual generated prelaunch blocks. Both witnesses retain their
physical block, activation, no-crossing state and literal launch date. -/
theorem prelaunchDownFailureAt_iff_suppressedDownAt (i : Fin (p.m - 1)) :
    (∃ r : Fin p.T, prelaunchDownFailureAt rate rewards C_star C_h z i r = true) ↔
      ∃ s : Fin (n_boot p), InitializationFailureProvenance.suppressedDownAt
          (sourceReferenceInput rate rewards C_star C_h z) s
          (ActualReferenceInitializationBlock.refFollower i) := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let f := ActualReferenceInitializationBlock.refFollower i
  constructor
  · rintro ⟨r, hd⟩
    obtain ⟨active, hpref, a, ha, d, hdblock, _hdate, haccept⟩ :=
      (prelaunchDownFailureAt_sameDateBlockDecisions rate rewards C_star C_h z i r).mp hd
    let s := roundBlockIndex p r
    let b := active.val.1.val
    let h := active.val.1.property.1
    have hboundary : b = ReferenceInitializationRun.run x s.val :=
      active.val.1.property.2.2
    have hRun : (ReferenceInitializationRun.run x s.val).completed < n_boot p := by
      exact hboundary ▸ h
    have hcross : b.crossing = none := active.val.1.property.2.1
    have hcompleted : b.completed = s.val := by
      have hprogress := run_progress x s.val s.isLt.le
      rcases hprogress with hc | hn
      · rw [← hboundary, hcross] at hc
        cases hc
      · exact (congrArg Boundary.completed hboundary).trans hn
    have hforced : b.forcedFailure f = false := by
      rw [hboundary]
      exact run_no_forced_before_launch x s.val
        (by rw [← hboundary]; exact hcross) f
    have hcrossRun : (ReferenceInitializationRun.run x s.val).crossing = none := by
      rw [← hboundary]
      exact hcross
    have hcompletedRun : (ReferenceInitializationRun.run x s.val).completed = s.val := by
      rw [← hboundary]
      exact hcompleted
    have hforcedRun : (ReferenceInitializationRun.run x s.val).forcedFailure f = false := by
      rw [← hboundary]
      exact hforced
    have haRun : (ReferenceInitializationRun.run x s.val).activation f = some a := by
      rw [← hboundary]
      exact ha
    have hdRun := generatedBlockDecision_mem_transport x b
      (ReferenceInitializationRun.run x s.val) h hRun f a ha haRun d hboundary hdblock
    have hlaunch := InitializationFailureProvenance.blockDecision_before_launch
      x s b h hboundary hcross hcompleted f a ha d hdblock
    have hsupp : InitializationFailureProvenance.suppressedDownAt x s f := by
      unfold InitializationFailureProvenance.suppressedDownAt
      refine ⟨hRun, hcrossRun, hcompletedRun, hforcedRun, a, haRun, d, hdRun,
        haccept, hlaunch⟩
    exact ⟨s, hsupp⟩
  · rintro ⟨s, hsupp⟩
    unfold InitializationFailureProvenance.suppressedDownAt at hsupp
    rcases hsupp with ⟨h, hcross, hcompleted, hforced, a, ha, d, hdblock,
      haccept, hstrict⟩
    let block := replayInput x
      (ReferenceInitializationRun.run x s.val) h f a ha
    obtain ⟨before, u, after, hlist, hdate, _hparsed⟩ :=
      (mem_decisions_iff
        (BootstrapPhysicalInput.sourceFollowerIndex p f) x.row a
        (ReferencePrelaunchPhysicalReplay.chronologicalHistory block)
        (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
          (nextBlock (ReferenceInitializationRun.run x s.val) h))
        (ReferencePrelaunchPhysicalReplay.blockIndices block)
        (ordinary x (ReferenceInitializationRun.run x s.val) f)
        d).mp hdblock
    have huMem : u ∈ ReferencePrelaunchPhysicalReplay.blockIndices block := by
      rw [hlist]
      simp
    have hbounds := InitializationFailureProvenance.blockIndices_member_bounds block huMem
    have htimeval : d.1.val = u.val := by
      calc
        d.1.val = (calendar
          (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
            (nextBlock (ReferenceInitializationRun.run x s.val) h)) u).val :=
              congrArg Fin.val hdate
        _ = u.val := rfl
    have hcalendar : d.1 ∈ BootstrapDimensions.calendarBlock p s := by
      rw [BootstrapDimensions.mem_calendarBlock_iff]
      have hlow : s.val * B_boot p ≤ d.1.val := by
        calc
          s.val * B_boot p ≤ u.val := by
            simpa only [x, ReferencePrelaunchPhysicalReplay.blockStart,
              nextBlock, hcompleted] using hbounds.1
          _ = d.1.val := htimeval.symm
      have hhigh : d.1.val < min p.T ((s.val + 1) * B_boot p) := by
        rw [htimeval]
        simpa only [x, ReferencePrelaunchPhysicalReplay.blockEnd,
          nextBlock, hcompleted] using hbounds.2
      exact ⟨hlow, hhigh⟩
    obtain ⟨s0, hs0, hunique⟩ :=
      BootstrapDimensions.round_mem_exactly_one_calendarBlock p d.1
    have hsEq : s = s0 := hunique s hcalendar
    have hrEq : roundBlockIndex p d.1 = s0 :=
      hunique (roundBlockIndex p d.1)
        (BootstrapDimensions.round_mem_quotient_block p d.1)
    have hindex : roundBlockIndex p d.1 = s := hrEq.trans hsEq.symm
    have hroundCross :
        (ReferenceInitializationRun.run x (roundBlockIndex p d.1).val).crossing = none := by
      simpa only [hindex] using hcross
    have hroundActivation :
        (ReferenceInitializationRun.run x (roundBlockIndex p d.1).val).activation f = some a := by
      simpa only [hindex] using ha
    have hprefExists : ∃ active : ActiveProjection p i d.1.val x.row
        (Nat.le_of_lt d.1.isLt) x (roundBlockIndex p d.1),
        source_prelaunch_down_prefix rate rewards C_star C_h z i d.1 =
          .inl (.inl active) := by
      cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i d.1 with
      | inl branch =>
        cases branch with
        | inl active => exact ⟨active, rfl⟩
        | inr inactive =>
          rcases inactive.property with ⟨_, hnone, _⟩
          have hboundary : inactive.val.1.val =
              ReferenceInitializationRun.run x (roundBlockIndex p d.1).val :=
            inactive.val.1.property.2.2
          have hnoneRun : (ReferenceInitializationRun.run x
              (roundBlockIndex p d.1).val).activation f = none := by
            rw [← hboundary]
            exact hnone
          rw [hroundActivation] at hnoneRun
          cases hnoneRun
      | inr stopped =>
        have hboundary : stopped.val.1 =
            ReferenceInitializationRun.run x (roundBlockIndex p d.1).val :=
          stopped.property.2.1
        have hcrossNe : (ReferenceInitializationRun.run x
            (roundBlockIndex p d.1).val).crossing ≠ none := by
          rw [← hboundary]
          exact stopped.property.1
        exact (hcrossNe hroundCross).elim
    obtain ⟨active, hpref⟩ := hprefExists
    rcases active.property with ⟨_, hactive, _, _⟩
    have hactiveRun : (ReferenceInitializationRun.run x
        (roundBlockIndex p d.1).val).activation f = some active.val.2.1 := by
      exact (congrArg (fun b' : Boundary p => b'.activation f)
        active.val.1.property.2.2).symm.trans hactive
    have hactivationEq : a = active.val.2.1 :=
      Option.some.inj (hroundActivation.symm.trans hactiveRun)
    subst a
    have hrunRemain : (ReferenceInitializationRun.run x
        (roundBlockIndex p d.1).val).completed < n_boot p := by
      simpa only [hindex] using h
    have hrunEq : ReferenceInitializationRun.run x
        (roundBlockIndex p d.1).val = ReferenceInitializationRun.run x s.val :=
      congrArg (fun k : Fin (n_boot p) => ReferenceInitializationRun.run x k.val) hindex
    have hdblockRun := generatedBlockDecision_mem_transport x
      (ReferenceInitializationRun.run x s.val)
      (ReferenceInitializationRun.run x (roundBlockIndex p d.1).val) h hrunRemain f
      active.val.2.1 ha hroundActivation d hrunEq.symm hdblock
    have hdblock' := generatedBlockDecision_mem_transport x
      (ReferenceInitializationRun.run x (roundBlockIndex p d.1).val)
      active.val.1.val hrunRemain active.val.1.property.1 f active.val.2.1
      hroundActivation hactive d active.val.1.property.2.2.symm hdblockRun
    have hsame := (prelaunchDownFailureAt_sameDateBlockDecisions
      rate rewards C_star C_h z i d.1).mpr
        ⟨active, hpref, active.val.2.1, hactive, d, hdblock', rfl, haccept⟩
    exact ⟨d.1, hsame⟩

/-- The detecting ordinary decision is not the same follower's after-block
forced correction. Other followers may still be corrected at that boundary. -/
theorem prelaunchDownFailureAt_not_forcedCorrectionAt (i : Fin (p.m - 1)) (r : Fin p.T)
    (hd : prelaunchDownFailureAt rate rewards C_star C_h z i r = true) :
    ¬ InitializationFailureProvenance.forcedCorrectionAt
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r)
      (ActualReferenceInitializationBlock.refFollower i) := by
  let x := sourceReferenceInput rate rewards C_star C_h z
  let f := ActualReferenceInitializationBlock.refFollower i
  obtain ⟨active, _, _⟩ := (prelaunchDownFailureAt_true_iff rate rewards C_star C_h z i r).mp hd
  have ha : (ReferenceInitializationRun.run x (roundBlockIndex p r).val).activation f =
      some active.val.2.1 :=
    (congrArg (fun b : Boundary p => b.activation f) active.val.1.property.2.2).symm.trans
      active.property.choose_spec.1
  intro hforce
  unfold InitializationFailureProvenance.forcedCorrectionAt at hforce
  obtain ⟨h, _, _, _, _, _, hf, _⟩ := hforce
  rw [activated_not_forced x _ h f active.val.2.1 ha] at hf
  cases hf

/-- A true readout's CURRENT decision has the absent DOWN word on the actual
physical branch. The coordinator's ordinary learner is absent and both the
coordinator and selected receiver take their tuple arms at this same round. -/
theorem prelaunchDownFailureAt_currentAbsentWord (i : Fin (p.m - 1)) (r : Fin p.T)
    (hd : prelaunchDownFailureAt rate rewards C_star C_h z i r = true) :
    ∃ active : ActiveProjection p i r.val (sourceReferenceInput rate rewards C_star C_h z).row
        (Nat.le_of_lt r.isLt) (sourceReferenceInput rate rewards C_star C_h z)
        (roundBlockIndex p r),
    source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inl (.inl active) ∧
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := active.val.1.val
    let a := active.val.2.1
    let f := ActualReferenceInitializationBlock.refFollower i
    let phy := physical x b active.val.1.property.1
    let own := ownEntry phy (PublicDiscreteDraws.followerPlayer p.two_le_m f) r
    ∃ test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p,
      test = ⟨r, (x.row.2 r).2 (0, i), none⟩ ∧ test.sent = none ∧
      (∀ w : AffineChannelLaw.Word (width p), test.sent ≠ some w) ∧
      ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a r own = some test ∧
      source_prelaunch_down_current_test rate rewards C_star C_h z i r = some test ∧
      coordinatorLearner b = none ∧
      BootstrapPhysicalBlock.actions phy (BootstrapPhysicalBlock.run phy r.val) r
          (ActiveRoundActions.coordinator p.two_le_m) =
        (BootstrapPhysicalBlock.tuple phy r).val (ActiveRoundActions.coordinator p.two_le_m) ∧
      BootstrapPhysicalBlock.actions phy (BootstrapPhysicalBlock.run phy r.val) r
          (PublicDiscreteDraws.followerPlayer p.two_le_m f) =
        (BootstrapPhysicalBlock.tuple phy r).val (PublicDiscreteDraws.followerPlayer p.two_le_m f) := by
  classical
  obtain ⟨active, hpref, w, M, _, hlen, _, _, _, _, _, _⟩ :=
    prelaunchDownFailureAt_completedBatch rate rewards C_star C_h z i r hd
  let x := sourceReferenceInput rate rewards C_star C_h z
  let b := active.val.1.val
  let a := active.val.2.1
  let own := ownEntry
    (physical x b active.val.1.property.1)
    (PublicDiscreteDraws.followerPlayer p.two_le_m
      (ActualReferenceInitializationBlock.refFollower i)) r
  let bank := active.val.2.2.2.downBatch
  let tr := traceAt i x.row a r own
  let tests := positiveAt p tr r
  let phy := physical x b active.val.1.property.1
  have hcensus := source_prelaunch_down_prefix_census rate rewards C_star C_h z i r
  rw [hpref] at hcensus
  dsimp only at hcensus
  rcases hcensus with ⟨_, _, _, hshort⟩
  change bank.pending.length < quota p at hshort
  have hlen' : bank.pending.length + tests.length = quota p := by
    simpa only [tests, tr, bank, List.length_append] using hlen
  have htestsPositive : 0 < tests.length := by omega
  have heligible : eligible (tr r) := by
    unfold tests positiveAt at htestsPositive
    split_ifs at htestsPositive with he
    · exact he
    · simp at htestsPositive
  have hcomponents :
      (downInput i x.row a r own).selected = true ∧
      (downInput i x.row a r own).receiverEnabled = true ∧
      0 < (downInput i x.row a r own).roundedReward := by
    simpa only [tr, traceAt,
      eligible] using heligible
  have hselected : (downInput i x.row a r own).selected = true :=
    hcomponents.1
  have hchoice : a.val ≤ r.val + 1 ∧
      PublicDiscreteDraws.slotDraw (x.row.2 r).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 r).1 = i := by
    change decide (a.val ≤ r.val + 1 ∧
      PublicDiscreteDraws.slotDraw (x.row.2 r).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 r).1 = i) = true at hselected
    exact of_decide_eq_true hselected
  have hpositive : 0 < own.2.val.val := by
    simpa only [downInput] using hcomponents.2.2
  have hslot : BootstrapPhysicalBlock.slot phy r = PublicDiscreteDraws.downSlot := by
    change PublicDiscreteDraws.slotDraw (x.row.2 r).1 = PublicDiscreteDraws.downSlot
    exact hchoice.2.1
  rcases active.property with ⟨_, hactivation, _, _⟩
  have hcross : b.crossing = none := active.val.1.property.2.1
  have hlearner : coordinatorLearner b = none := by
    simp only [coordinatorLearner, hcross,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  let f := ActualReferenceInitializationBlock.refFollower i
  have hnot : f ∉ phy.uninformed := by
    change f ∉ uninformed b
    rw [mem_uninformed, hactivation]
    intro he
    cases he
  have hcoord := (BootstrapPhysicalBlock.actions_coordinator phy
    (BootstrapPhysicalBlock.run phy r.val) r).trans
      (BootstrapPhysicalBlock.coordinatorAction_down phy
        (BootstrapPhysicalBlock.run phy r.val) r hslot)
  have hreceiver :
      BootstrapPhysicalBlock.actions phy (BootstrapPhysicalBlock.run phy r.val) r
          (PublicDiscreteDraws.followerPlayer p.two_le_m f) =
        (BootstrapPhysicalBlock.tuple phy r).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m f) := by
    calc
      _ = BootstrapPhysicalBlock.followerAction phy r f :=
        BootstrapPhysicalBlock.actions_follower phy
          (BootstrapPhysicalBlock.run phy r.val) r f
      _ = BootstrapPhysicalBlock.unoccupiedAction phy r f := by
        simp only [BootstrapPhysicalBlock.followerAction, dite_eq_right hnot]
      _ = (BootstrapPhysicalBlock.tuple phy r).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m f) :=
        BootstrapPhysicalBlock.unoccupiedAction_down phy r f hslot
  let test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p :=
    ⟨r, (x.row.2 r).2 (0, i), none⟩
  have htest : ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a r own = some test := by
    simp only [ReferenceGeneratedPrelaunchDownCohort.prelaunchTest,
      hselected, hpositive, and_self, ↓reduceIte]
    rfl
  have hcurrent : source_prelaunch_down_current_test rate rewards C_star C_h z i r =
      some test := by
    simpa only [source_prelaunch_down_current_test, hpref] using htest
  refine ⟨active, hpref, test, rfl, rfl, ?_, htest, hcurrent, hlearner, hcoord, hreceiver⟩
  intro w hsent
  cases hsent

/-- On an active prefix, false means there is no passing ordinary parse: this
includes an incomplete batch, an invalid DOWN parse, and a parsed record that
the ordinary start/calendar test rejects. -/
theorem prelaunchDownFailureAt_false_iff
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row
      (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r))
    (hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r =
      .inl (.inl active)) :
    prelaunchDownFailureAt rate rewards C_star C_h z i r = false ↔
      parsedAt rate.eta i
          (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r
          (ownEntry
            (physical
              (sourceReferenceInput rate rewards C_star C_h z)
              active.val.1.val active.val.1.property.1)
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r)
          active.val.2.2.2.downBatch = none ∨
        ∀ M, parsedAt rate.eta i
            (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r
            (ownEntry
              (physical
                (sourceReferenceInput rate rewards C_star C_h z)
                active.val.1.val active.val.1.property.1)
              (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ActualReferenceInitializationBlock.refFollower i)) r)
            active.val.2.2.2.downBatch = some M →
          ¬ OrdinaryMessageCodec.acceptDown
            (ReferencePrelaunchFollower.codecParams p rate.eta) 0 (r.val + 1) M := by
  classical
  rw [prelaunchDownFailureAt, hpref]
  rw [decide_eq_false_iff_not]
  unfold passing_at
  constructor
  · intro hnot
    right
    intro M hparsed haccept
    exact hnot ⟨M, hparsed, haccept⟩
  · rintro (hnone | hreject) ⟨M, hparsed, haccept⟩
    · rw [hnone] at hparsed
      cases hparsed
    · exact hreject M hparsed haccept

/-- These are the three nonpassing outcomes on the actual active call:
no raw output (which includes incompletion), an invalid DOWN parse, or a
unique raw output whose parsed start/calendar test is locally rejected. -/
theorem prelaunchDownFailureAt_false_cases (i : Fin (p.m - 1)) (r : Fin p.T)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inl (.inl active)) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let cp := ReferencePrelaunchFollower.codecParams p rate.eta
    let own := ownEntry
      (physical x active.val.1.val active.val.1.property.1)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) r
    let raw := (decodeAt i x.row active.val.2.1 r own
      active.val.2.2.2.downBatch).2
    prelaunchDownFailureAt rate rewards C_star C_h z i r = false ↔
      raw = none ∨ (∃ w, raw = some w ∧ OrdinaryMessageCodec.parseDown cp
        (some ((OrdinaryMessageCodec.wordEquivFlat cp).symm w)) = none) ∨
      (∃ w M, raw = some w ∧ OrdinaryMessageCodec.parseDown cp
        (some ((OrdinaryMessageCodec.wordEquivFlat cp).symm w)) = some M ∧
        ¬ OrdinaryMessageCodec.acceptDown cp 0 (r.val + 1) M) := by
  classical
  intro x cp own raw
  rw [prelaunchDownFailureAt, hpref, decide_eq_false_iff_not]
  change (¬ ∃ M, OrdinaryMessageCodec.parseDown cp
    (raw.map (OrdinaryMessageCodec.wordEquivFlat cp).symm) = some M ∧
    OrdinaryMessageCodec.acceptDown cp 0 (r.val + 1) M) ↔ _
  constructor
  · intro hnot
    by_cases hnone : raw = none
    · exact Or.inl hnone
    · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists.mp hnone
      have hr := hw.symm
      cases hm : OrdinaryMessageCodec.parseDown cp
          (some ((OrdinaryMessageCodec.wordEquivFlat cp).symm w)) with
      | none => exact Or.inr (Or.inl ⟨w, hr, hm⟩)
      | some M =>
        refine Or.inr (Or.inr ⟨w, M, hr, hm, ?_⟩)
        intro ha
        apply hnot
        refine ⟨M, ?_, ha⟩
        rw [hr]
        exact hm
  · rintro (hnone | ⟨w, hw, hnone⟩ | ⟨w, M, hw, hm, hreject⟩) ⟨M', hparse, ha⟩
    · rw [hnone] at hparse
      change none = some M' at hparse
      cases hparse
    · rw [hw] at hparse
      change OrdinaryMessageCodec.parseDown cp
        (some ((OrdinaryMessageCodec.wordEquivFlat cp).symm w)) = some M' at hparse
      rw [hnone] at hparse
      cases hparse
    · rw [hw] at hparse
      have he : M = M' := Option.some.inj (hm.symm.trans hparse)
      subst M'
      exact hreject ha

/-- An incomplete call keeps exactly the appended partial bank and emits no
raw word. This is an operational case, with its size condition exposed. -/
theorem prelaunchDownDecodeAt_incomplete (i : Fin (p.m - 1)) (r : Fin p.T)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r)) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let own := ownEntry
      (physical x active.val.1.val active.val.1.property.1)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) r
    let bank := active.val.2.2.2.downBatch
    let tr := traceAt i x.row active.val.2.1 r own
    let B := bank.pending ++ positiveAt p tr r
    B.length < quota p → decodeAt i x.row active.val.2.1 r own bank =
        (⟨B, bank.completed⟩, none) := by
  classical
  intro x own bank tr B hB
  unfold decodeAt
  split_ifs with hs
  · change (if B.length < quota p then _ else _,
      if B.length < quota p then _ else _) = _
    rw [ite_eq_left hB, ite_eq_left hB]
  · have he : ¬ eligible (tr r) := fun h => hs h.1
    have hnil : positiveAt p tr r = [] := by
      simp only [positiveAt, he, ↓reduceIte]
    have hbank : B = bank.pending := by simp only [B, hnil, List.append_nil]
    rw [hbank]

/-- A completed ordinary decoder call clears its pending bank independently
of whether its exact raw solver result is `some` or `none`. -/
theorem prelaunchDownDecodeAt_complete_clears (i : Fin (p.m - 1)) (r : Fin p.T)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hselected : let x := sourceReferenceInput rate rewards C_star C_h z
      let own := ownEntry (physical x active.val.1.val active.val.1.property.1)
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) r
      (downInput i x.row active.val.2.1 r own).selected = true)
    (heligible : let x := sourceReferenceInput rate rewards C_star C_h z
      let own := ownEntry (physical x active.val.1.val active.val.1.property.1)
        (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)) r
      eligible (traceAt i x.row active.val.2.1 r own r))
    (hquota : active.val.2.2.2.downBatch.pending.length + 1 = quota p) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let own := ownEntry (physical x active.val.1.val active.val.1.property.1)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) r
    let bank := active.val.2.2.2.downBatch
    let tr := traceAt i x.row active.val.2.1 r own
    decodeAt i x.row active.val.2.1 r own bank =
        (⟨[], bank.completed ++ [bank.pending ++ [entry p tr r]]⟩,
          batchOutput (bank.pending ++ [entry p tr r])) := by
  intro x own bank tr
  rw [decodeAt, ite_eq_left hselected]
  exact decodeStep_complete p tr bank r heligible hquota

/-- Every source-prefix DOWN test stores no encoded assignment word. A test is
retained only as the actual selected positive sample; its missing word is
separate from the physical provenance theorem for the current decision above. -/
private theorem prelaunchTest_sent_none
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (a : Activation p) (t : Fin p.T)
    (own : Fin p.K × Observation p) (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (h : ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i row a t own = some test) :
    test.sent = none := by
  unfold ReferenceGeneratedPrelaunchDownCohort.prelaunchTest at h
  by_cases hcond :
      (downInput i row a t own).selected = true ∧
        0 < own.2.val.val
  · simp only [hcond, and_self, reduceIte, Option.some.injEq] at h
    cases h
    rfl
  · simp only [hcond, ite_false] at h
    cases h

private theorem boundaryPrelaunchDownTests_sent_none (x : Input p)
    (b : Boundary p) (i : Fin (p.m - 1)) (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (h : test ∈ ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests x b i) :
    test.sent = none := by
  classical
  let f := ActualReferenceInitializationBlock.refFollower i
  cases hf : b.forcedFailure f with
  | false =>
      cases ha : b.activation f with
      | none => simp [ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests,
          f, hf, ha] at h
      | some a =>
          have hmem : test ∈ (List.ofFn (fun u : Fin
              (elapsed p b.completed) => u)).filterMap
              (fun u => ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a
                (calendar
                  (elapsed_le_T p b.completed) u)
                (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f) u)) := by
            simpa only [ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests,
              f, hf, ha, Bool.false_eq_true, ↓reduceIte] using h
          rcases List.mem_filterMap.mp hmem with ⟨u, _, htest⟩
          exact prelaunchTest_sent_none i x.row a
            (calendar
              (elapsed_le_T p b.completed) u)
            (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f) u)
            test htest
  | true =>
      simp [ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests,
        f, hf] at h

theorem source_prelaunch_down_prefix_tests_sent_none (i : Fin (p.m - 1)) (r : Fin p.T)
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (hmem : test ∈ source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r) :
    test.sent = none := by
  classical
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hmem' : test ∈
              (List.ofFn (fun u : Fin r.val => u)).filterMap (fun u =>
                ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i
                  (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1
                  (calendar (Nat.le_of_lt r.isLt) u)
                  (active.val.2.2.1 u)) := by
            simpa only [source_prelaunch_down_prefix_tests, hpref] using hmem
          obtain ⟨u, _, htest⟩ := List.mem_filterMap.mp hmem'
          exact prelaunchTest_sent_none i
            (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1
            (calendar (Nat.le_of_lt r.isLt) u)
            (active.val.2.2.1 u) test htest
      | inr inactive => simp [source_prelaunch_down_prefix_tests, hpref] at hmem
  | inr stopped =>
      have hmem' : test ∈
          ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
            (sourceReferenceInput rate rewards C_star C_h z) stopped.val.1 i := by
        simpa only [source_prelaunch_down_prefix_tests, hpref] using hmem
      exact boundaryPrelaunchDownTests_sent_none
        (sourceReferenceInput rate rewards C_star C_h z) stopped.val.1 i test hmem'

/-- No test in the actual strict-prefix DOWN list carries any fixed awaited
word as an ordinary encoded assignment. -/
theorem source_prelaunch_down_prefix_no_fixed_sent_word (i : Fin (p.m - 1)) (r : Fin p.T)
    (w : AffineChannelLaw.Word (width p)) :
    ∀ test ∈ source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r,
      test.sent ≠ some w := by
  intro test htest
  rw [source_prelaunch_down_prefix_tests_sent_none
    rate rewards C_star C_h z i r test htest]
  intro h
  cases h

/-- Absence of a sent word includes the current physical test, even at `T`.
No next-round prefix or launch is required. -/
theorem source_prelaunch_down_tests_through_sent_none (i : Fin (p.m - 1)) (r : Fin p.T)
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (ht : test ∈ source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
      (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList) :
    test.sent = none := by
  rcases List.mem_append.mp ht with hp | hc
  · exact source_prelaunch_down_prefix_tests_sent_none rate rewards C_star C_h z i r test hp
  · have hc' : source_prelaunch_down_current_test rate rewards C_star C_h z i r = some test := by
      simpa only [Option.mem_toList, Option.mem_def] using hc
    cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | inl branch =>
      cases branch with
      | inl active =>
        simp only [source_prelaunch_down_current_test, hpref] at hc'
        exact prelaunchTest_sent_none _ _ _ _ _ test hc'
      | inr inactive => simp only [source_prelaunch_down_current_test, hpref, reduceCtorEq] at hc'
    | inr stopped => simp only [source_prelaunch_down_current_test, hpref, reduceCtorEq] at hc'

/-- No actual prelaunch completed DOWN batch was sent as one fixed word.
The assertion is stronger than needed for an awaited word: every positive
would first need an ordinary encoded word, whereas all actual tests have none.
The census supplies the real quota and hence a nonempty completed batch. -/
theorem source_prelaunch_down_no_fixed_word_completed_batch (i : Fin (p.m - 1)) (r : Fin p.T) :
    let tests := source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
      (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let x := sourceReferenceInput rate rewards C_star C_h z
        let own := ownEntry (physical x active.val.1.val active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r
        let bank := active.val.2.2.2.downBatch
        let B := bank.pending ++ positiveAt p (traceAt i x.row active.val.2.1 r own) r
        ¬ ∃ batch, (batch ∈ bank.completed ∨ batch = B ∧ B.length = quota p) ∧
          ∃ w : AffineChannelLaw.Word (width p), ∀ e ∈ batch,
            ∃ test ∈ tests, ReferenceGeneratedPrelaunchDownCohort.testEntry test = e ∧
              test.sent = some w
    | .inl (.inr _) => True
    | .inr stopped =>
        ¬ ∃ batch ∈ stopped.val.2.downBatch.completed,
          ∃ w : AffineChannelLaw.Word (width p), ∀ e ∈ batch,
            ∃ test ∈ tests, ReferenceGeneratedPrelaunchDownCohort.testEntry test = e ∧
              test.sent = some w := by
  intro tests
  have noFixed (batch : List (Entry p.T (width p))) (hlen : batch.length = quota p) :
      ¬ ∃ w : AffineChannelLaw.Word (width p), ∀ e ∈ batch,
        ∃ test ∈ tests, ReferenceGeneratedPrelaunchDownCohort.testEntry test = e ∧
          test.sent = some w := by
    rintro ⟨w, hsent⟩
    cases batch with
    | nil => have := quota_pos p; simp only [List.length_nil] at hlen; omega
    | cons e rest =>
      obtain ⟨test, ht, _, hw⟩ := hsent e (by simp only [List.mem_cons_self])
      rw [source_prelaunch_down_tests_through_sent_none rate rewards C_star C_h z i r test ht] at hw
      cases hw
  have hc := source_prelaunch_down_prefix_census rate rewards C_star C_h z i r
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
    cases branch with
    | inl active =>
      rw [hpref] at hc
      rintro ⟨batch, hb | ⟨rfl, hB⟩, hsent⟩
      · exact noFixed batch (hc.2.2.1 batch hb) hsent
      · exact noFixed _ hB hsent
    | inr inactive => trivial
  | inr stopped =>
    rw [hpref] at hc
    rintro ⟨batch, hb, hsent⟩
    exact noFixed batch (hc.2.2.1 batch hb) hsent

/-- A raw `none` can mean no satisfying affine solution or multiple
satisfying solutions; it never by itself certifies ambiguity. -/
theorem prelaunchDownRawNone_iff_empty_or_ambiguous (batch : List (Entry p.T (width p))) :
    batchOutput batch = none ↔ (∀ w, ¬ satisfies (samples batch) w) ∨
      ∃ w v, satisfies (samples batch) w ∧ satisfies (samples batch) v ∧ w ≠ v := by
  simpa only [batchOutput] using
    (solve_eq_none_iff_empty_or_ambiguous
      (samples batch))

/-- The actual initialization coordinator has no UP receiver in any boundary.
The selected follower's ordinary offer remains the literal empty placeholder;
this makes no claim about `acceptUp` on arbitrary supplied contexts. -/
theorem prelaunchCoordinatorUpDisabled (b : Boundary p) : coordinatorUpEnabled b = false := rfl

/-- The physical process starts with the literal zero UP record itself. -/
theorem prelaunchActualInitialUpPlaceholder : BootstrapPhysicalBlock.initialUpRecord p =
      ⟨OrdinaryMessageCodec.upPlaceholder, Or.inl rfl⟩ := rfl

theorem prelaunchFollowerUpOffer_isPlaceholder (eta : LearningRate)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (a : Activation p) (r : Fin p.T)
    (M : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p eta))
    (hoff : upOffer eta i row a r = some M) : M.val = OrdinaryMessageCodec.upPlaceholder :=
  upOffer_fields eta i row a r M hoff

/-- On the actual active selected-UP branch the follower sends the physical
initial placeholder. The coordinator receiver remains disabled, so this
placeholder cannot be an awaited UP word. These are branch inputs only;
no assertion about arbitrary `acceptUp` contexts is used. -/
theorem prelaunch_active_up_sender (i : Fin (p.m - 1)) (r : Fin p.T)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r)) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let b := active.val.1.val
    let f := ActualReferenceInitializationBlock.refFollower i
    let phy := physical x b active.val.1.property.1
    BootstrapPhysicalBlock.slot phy r = PublicDiscreteDraws.upSlot →
      BootstrapPhysicalBlock.selected phy r = f → coordinatorUpEnabled b = false ∧
      (BootstrapPhysicalBlock.initialUpRecord p).val = OrdinaryMessageCodec.upPlaceholder ∧
      BootstrapPhysicalBlock.actions phy (BootstrapPhysicalBlock.run phy r.val) r
          (PublicDiscreteDraws.followerPlayer p.two_le_m f) = ActiveRoundActions.sendArm
          (AffineChannelLaw.affineHash ((x.row.2 r).2 (1, f))
            (BootstrapPhysicalBlock.initialUpWord p))
          ((BootstrapPhysicalBlock.tuple phy r).val (PublicDiscreteDraws.followerPlayer p.two_le_m f))
          ((BootstrapPhysicalBlock.tuple phy r).val (ActiveRoundActions.coordinator p.two_le_m)) := by
  intro x b f phy hslot hselected
  have ha := active.property.choose_spec.1
  have hnot : f ∉ phy.uninformed := by
    change f ∉ uninformed b
    rw [mem_uninformed, ha]
    intro h
    cases h
  refine ⟨rfl, rfl, ?_⟩
  rw [BootstrapPhysicalBlock.actions_follower, BootstrapPhysicalBlock.followerAction,
    dite_eq_right hnot]
  rw [← hselected]
  have hs := BootstrapPhysicalBlock.unoccupiedAction_selected_up phy r hslot
  change BootstrapPhysicalBlock.unoccupiedAction phy r (BootstrapPhysicalBlock.selected phy r) =
    ActiveRoundActions.sendArm
      (BootstrapPhysicalBlock.initialUpBit phy r (BootstrapPhysicalBlock.selected phy r)) _ _
  rw [BootstrapPhysicalBlock.initialUpBit_eq_offset]
  exact hs

/-- The dated flag is empty before round zero. -/
theorem prelaunchPastDecoderFlag_zero (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    prelaunchPastDecoderFlag rate rewards C_star C_h z 0 (Nat.zero_le p.T) = false := by
  simp [prelaunchPastDecoderFlag]

/-- Extending the strict past by one source round adds exactly its decision
bit. Thus a decision at round `n` first appears in the flag for `n + 1`. -/
theorem prelaunchPastDecoderFlag_succ (n : ℕ) (hn : n + 1 ≤ p.T) :
    prelaunchPastDecoderFlag rate rewards C_star C_h z (n + 1) hn =
      (prelaunchPastDecoderFlag rate rewards C_star C_h z n (Nat.le_of_succ_le hn) ||
        decide (∃ i : Fin (p.m - 1),
          prelaunchDownFailureAt rate rewards C_star C_h z i ⟨n, hn⟩ = true)) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [prelaunchPastDecoderFlag, decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨j, i, hj⟩
    by_cases hlt : j.val < n
    · left
      refine ⟨⟨j.val, hlt⟩, i, ?_⟩
      have hcast : Fin.castLE hn j =
          Fin.castLE (Nat.le_of_succ_le hn) ⟨j.val, hlt⟩ := by
        apply Fin.ext
        rfl
      rw [hcast] at hj
      exact hj
    · right
      have hjn : j.val = n := by omega
      have hcast : Fin.castLE hn j = (⟨n, hn⟩ : Fin p.T) := by
        apply Fin.ext
        exact hjn
      refine ⟨i, ?_⟩
      rw [← hcast]
      exact hj
  · rintro (⟨j, i, hj⟩ | ⟨i, hi⟩)
    · refine ⟨Fin.castLE (by omega : n ≤ n + 1) j, i, ?_⟩
      have hcast : Fin.castLE hn (Fin.castLE (by omega : n ≤ n + 1) j) =
          Fin.castLE (Nat.le_of_succ_le hn) j := by
        apply Fin.ext
        rfl
      rw [hcast]
      exact hj
    · refine ⟨Fin.last n, i, ?_⟩
      have hcast : Fin.castLE hn (Fin.last n) = (⟨n, hn⟩ : Fin p.T) := by
        apply Fin.ext
        rfl
      rw [hcast]
      exact hi

end Bandits.Support.ReferencePrelaunchDownDecisionReadout

end
