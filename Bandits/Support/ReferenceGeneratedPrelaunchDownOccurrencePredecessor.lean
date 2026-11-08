/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrenceTail

import Lean.Elab.Tactic.Omega

/-!
# Actual fixed-birth prelaunch DOWN predecessor detector

This module supplies the deterministic predecessor step for the literal
predictable indicator and occurrence events of the imported module. A
nonempty pending cohort with all required flags has an earlier actual positive
test carrying the last of those flags. The argument descends actual calendar
prefixes, using the active census and the active/inactive/stopped bridges.

The descent stops at the actual empty-bank birth already required by the
indicator. It neither assumes an ancestry law nor identifies a naturally empty
old bank with a fresh birth. A quota clear cannot produce the nonempty endpoint,
irrespective of the solver's output. An inactive-to-active transition starts
from the actual initial empty bank; a stopped prefix cannot become active.

All events, the source point, the selected row, and the deterministic candidate
are the existing objects. There is no replacement execution or event and no
measure statement here. The final count bound uses the imported occurrence
uniqueness and the predecessor inclusion proved below.

Mathematical sources in `sources/zip4/manuscript/`:
* `appendix_a_local_protocol.tex:111-153`: preceding detector and unique test;
* `appendix_b_communication.tex:724-736`: prelaunch DOWN specialization;
* `07_public_setup.tex:60-112,127-164`: real activation and reference execution;
* `05_binary_transport.tex:20-42`: append, quota clearing, and solver-none paths.

These are internal deterministic results. They do not assert a probability
recurrence, a mixed launch join, or manuscript theorem closure.

## Inputs and fixed objects

The common parameters of the exports are the original `p`, `rate`, whole
rounded `rewards` table, unrestricted `C_star` and `C_h`, channel `i`, birth
calendar index `alpha`, completed-batch ordinal `k`, level `q`, bounded-birth
proof `hAlpha`, and deterministic word `w`. Pointwise exports also take the
original complete source `z`. Occurrence exports take an actual `r : Fin p.T`.

The strong producer takes exactly `2 ≤ q` and the existing predictable
indicator. It does not require current positivity. The general predecessor
takes exactly `1 ≤ q` and the existing occurrence. The subset and count bounds
take exactly `1 ≤ q`, with their source points and occurrence witnesses
quantified in their conclusions. In particular, none of these exports takes
an ancestry relation, bank law, flag law, assumed event inclusion, decoder
success, later completion, or launch witness.

The inherited indicator contains the actual birth readout, the active-prefix
tag, both level bounds, the completed ordinal, the bank birth, the pending
length, and every preceding flag. These are consumed from that same indicator
throughout the descent. No bound on `q` relative to quota is supplied anew.
The prior occurrence uses `q - 1` with precisely the same `alpha`, `k`, and `w`.

The current test is identified through the public current-pair theorem with
the affine pair from the original selected row `J(z)`. The candidate word is
never selected by a later decoder result. The full source point retains all
public rows and original private coordinates, including the scalar selecting
`J`; this proof neither replaces coordinates nor takes a marginal law.

## Local proof inputs

`past_indicator_strict_after_birth` consumes only `2 ≤ q` and the indicator
at its actual endpoint. Equality of the endpoint and birth indices identifies
their actual prefixes, so the birth's empty bank contradicts the pending length.

`past_indicator_successor_of_active` additionally takes the real predecessor
projection and an explicit equality identifying it with the generated prefix.
The complete one-step helper discharges that equality by case analysis on the
actual prefix. Its clock conditions are `r.val + 1 < p.T` and `alpha ≤ r.val`.
It accepts no arbitrary state, trace, history, or transition specification.

`past_indicator_successor_not_inactive` consumes the next indicator and
`2 ≤ q`. It obtains the empty initial state from the inactive bridge, rather
than assuming that new activations reset correctly. This also covers genuine
declaration transitions at block boundaries.

`past_indicator_successor_not_stopped` consumes the next indicator and the
existence of that next calendar index. It obtains persistent stopping from the
stopped bridge. It needs no positivity or no-stop assumption.

`past_indicator_successor_cases` composes those three real predecessor cases.
The public strong induction supplies its clock bounds from strict lateness
after birth, and supplies each next indicator by equality of calendar indices.
Only the gap case recurses, with a strictly smaller calendar value.

## Endpoints and remaining assembly

At `q = 1`, the existing first-level theorem gives exactly the actual birth
detector. At `q ≥ 2`, a nonempty bank forces strict lateness after birth, so the
predecessor calendar index is formed only when it exists. This also handles
zero without adding an initialization producer or assuming an active prefix
there. At terminal birth `alpha = p.T`, the indicator's own clock inequality
already rules out every `Fin p.T` endpoint. No action at `p.T` is introduced.

The zero detector remains the imported actual birth event, including terminal
birth mass. Positive detectors remain existence of actual hashed occurrences;
neither natural emptiness nor future completion changes those definitions.

The intended recurrence consumer must separately supply the exact source mass
identity and its measure assembly. The all-times same-birth interval and its
launch join are also separate work. Neither is assumed or proved here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrencePredecessor

open ConstructorDimensions BootstrapDimensions
open ReferenceGeneratedPrelaunchDownPrefix
open ReferenceGeneratedPrelaunchDownOccurrenceTail
open ReferenceGeneratedPrelaunchDownCurrentPair
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

/-- At its own actual birth the bank is empty. Hence a predictable indicator
with at least one pending entry must be strictly later than that birth. The
only hypotheses beyond the original data are the level bound and the literal
indicator; in particular no historical bank identification is supplied. -/
private theorem past_indicator_strict_after_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star : ℝ)
    (C_h : ℝ)
    (i : Fin (p.m - 1))
    (alpha : ℕ)
    (k : ℕ)
    (q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T)
    (hq : 2 ≤ q)
    (hI : source_prelaunch_down_past_indicator rate rewards C_star C_h z i
      alpha k q hAlpha r w) : alpha < r.val := by
  classical
  rcases hI with ⟨_, _, har, hbirth, hbank⟩
  by_contra hnot
  have heq : alpha = r.val := by omega
  subst alpha
  -- The birth and endpoint now refer to the very same actual calendar prefix.
  -- Dependent projection types therefore agree before the bank fields are read.
  simp only [birthAt, dite_eq_left r.isLt, Fin.eta] at hbirth
  cases hpref : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          rw [hpref] at hbank hbirth
          have hpending := hbirth.2.1
          have hlength := hbank.2.2.1
          rw [hpending, List.length_nil] at hlength
          omega
      | inr _ =>
          rw [hpref] at hbank
          exact hbank.elim
  | inr _ =>
      rw [hpref] at hbank
      exact hbank.elim

/-- The active case of one backward calendar step. The projection is explicitly
identified with the actual prefix by `hprefix`, rather than supplied as an
arbitrary state. The next literal indicator is the only bank/flag input.
The clock bound `alpha ≤ r.val` is discharged by the public descent. -/
private theorem past_indicator_successor_of_active
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star : ℝ)
    (C_h : ℝ)
    (i : Fin (p.m - 1))
    (alpha : ℕ)
    (k : ℕ)
    (q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T)
    (hnext : r.val + 1 < p.T)
    (har : alpha ≤ r.val)
    (hq : 2 ≤ q)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hprefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r =
      .inl (.inl active))
    (hI : source_prelaunch_down_past_indicator rate rewards C_star C_h z i
      alpha k q hAlpha ⟨r.val + 1, hnext⟩ w) :
    source_prelaunch_down_past_indicator rate rewards C_star C_h z i
        alpha k q hAlpha r w ∨
      prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q - 1)
        hAlpha w z r := by
  classical
  let rn : Fin p.T := ⟨r.val + 1, hnext⟩
  change source_prelaunch_down_past_indicator rate rewards C_star C_h z i
    alpha k q hAlpha rn w at hI
  rcases hI with ⟨hqone, hqquota, _, hbirth, hendpoint⟩
  cases hnextPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
  | inl nextBranch =>
      cases nextBranch with
      | inr _ =>
          rw [hnextPrefix] at hendpoint
          exact hendpoint.elim
      | inl nextActive =>
          rw [hnextPrefix] at hendpoint
          rcases hendpoint with ⟨hcompletedNext, hbirthNext, hlengthNext, hgoodNext⟩
          -- Every local name below is a projection of the identified actual
          -- prefix or its prescribed physical step, rather than new run data.
          let x := sourceReferenceInput rate rewards C_star C_h z
          let a := active.val.2.1
          let state := active.val.2.2.2
          let own := ReferenceInitializationRun.ownEntry
            (ReferenceInitializationRun.physical x active.val.1.val
              active.val.1.property.1)
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r
          let tr := ReferencePrelaunchFollower.traceAt i x.row a r own
          let bank := state.downBatch
          let next := (ReferencePrelaunchFollower.step i x.row a r own state).downBatch
          let current := source_prelaunch_down_current_test rate rewards C_star C_h z i r
          let tests := source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r
          let nextFlags := (tests ++ current.toList).map
            (fun test => (test.sent ≠ some w,
              AffineChannelLaw.affineHash test.sample w = 1)) |>.drop
            (AffineBatchDecoder.quota p * next.completed.length)
          -- The active bridge crosses real block boundaries as well as gaps
          -- inside blocks. In its active successor case it preserves activation
          -- and identifies the entire ordinary state with the actual step.
          have hbridge :=
            ReferenceGeneratedPrelaunchDownActiveBridge.source_prelaunch_down_active_successor
              rate rewards C_star C_h z i r hnext
          rw [hprefix] at hbridge
          have htests := hbridge.2.2.2.1
          have htransition := hbridge.2.2.2.2
          dsimp only [rn] at hnextPrefix
          rw [hnextPrefix] at htransition
          have hactivation : nextActive.val.2.1 = a := htransition.2.2.1
          have hstate : nextActive.val.2.2.2 =
              ReferencePrelaunchFollower.step i x.row a r own state := htransition.2.2.2
          have hbank : nextActive.val.2.2.2.downBatch = next :=
            congrArg ReferencePrelaunchFollower.State.downBatch hstate
          have hcompleted : next.completed.length = k := by
            rw [← hbank]
            exact hcompletedNext
          have hbankBirth : bankBirth a next = some alpha := by
            rw [← hbank, ← hactivation]
            exact hbirthNext
          have hlength : next.pending.length = q - 1 := by
            rw [← hbank]
            exact hlengthNext
          -- Translate the endpoint's cohort flags through the actual appended
          -- test census. The drop index uses this same next completed ordinal.
          have hflagsEq :
              source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i rn w =
                nextFlags := by
            simp only [source_prelaunch_down_current_cohort_flags, rn, hnextPrefix]
            rw [source_prelaunch_down_prefix_flags, htests, hbank]
          have hgood : List.Forall (fun flags => flags.1 ∧ flags.2) nextFlags := by
            rw [← hflagsEq]
            exact hgoodNext
          -- The census distinguishes ineligible gaps, eligible subquota
          -- appends, and quota clears independently of the decoder result.
          have hcensus :=
            ReferenceGeneratedPrelaunchDownCohortStep.source_prelaunch_down_active_step_census
              rate rewards C_star C_h z i r
          rw [hprefix] at hcensus
          rcases hcensus with
            ⟨_, _, _, _, _, _, _, hcurrent, _, hgap, hquota, hsubquota, hclear, hflags⟩
          change current = (if AffineBatchDecoder.eligible (tr r) then
            some ⟨r, (tr r).sample, none⟩ else none) at hcurrent
          have hflagData := hflags w
          rcases hflagData with ⟨_, _, _, hflagGap, hflagSubquota, _⟩
          by_cases heligible : AffineBatchDecoder.eligible (tr r)
          · rcases hquota heligible with hshort | hfull
            · rcases hsubquota heligible hshort with
                ⟨hpending, _, hcomp, hborn, _⟩
              -- A single appended equation accounts for the last pending
              -- entry. All earlier entries remain in the same completed ordinal.
              have hlengthOld : bank.pending.length = (q - 1) - 1 := by
                change next.pending = bank.pending ++ [AffineBatchDecoder.entry p tr r]
                  at hpending
                rw [hpending, List.length_append, List.length_singleton] at hlength
                omega
              have hflagsAppend : nextFlags =
                  source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i r w ++
                    [((none : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) ≠
                        some w, AffineChannelLaw.affineHash (tr r).sample w = 1)] :=
                hflagSubquota heligible hshort
              rw [hflagsAppend] at hgood
              have hgoodOld : List.Forall (fun flags => flags.1 ∧ flags.2)
                  (source_prelaunch_down_current_cohort_flags
                    rate rewards C_star C_h z i r w) :=
                (List.forall_append.mp hgood).1
              have hcurrentFlag :
                  (none : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) ≠ some w ∧
                    AffineChannelLaw.affineHash (tr r).sample w = 1 :=
                (List.forall_append.mp hgood).2
              have hhash : AffineChannelLaw.affineHash (tr r).sample w = 1 :=
                hcurrentFlag.2
              -- The weaker level bounds are derived here from the given
              -- indicator's quota bound and the explicit nonempty-level bound.
              have hIprevious : source_prelaunch_down_past_indicator rate rewards C_star C_h z i
                  alpha k (q - 1) hAlpha r w := by
                refine ⟨by omega, by omega, har, hbirth, ?_⟩
                rw [hprefix]
                refine ⟨?_, ?_, hlengthOld, hgoodOld⟩
                · exact hcomp.symm.trans hcompleted
                · exact hborn.symm.trans hbankBirth
              have hpositive : A_r rate rewards C_star C_h z i r := by
                change current.isSome = true
                rw [hcurrent, ite_eq_left heligible]
                rfl
              -- Recover the original selected-J pair from this actual current
              -- positive test. No future word or off-J sample is substituted.
              have hcanonical := current_test_eq_some_of_selected_positive
                rate rewards C_star C_h z i r
                (ActualInitializationPhysicalStep.selectedRowIndex p z) rfl hpositive
              change current = _ at hcanonical
              rw [hcurrent, ite_eq_left heligible] at hcanonical
              have hsample := congrArg
                ReferenceGeneratedDownBatchCalendar.ExecutedTest.sample
                (Option.some.inj hcanonical)
              refine Or.inr ⟨⟨hIprevious, hpositive⟩, ?_⟩
              exact (congrArg (fun sample => AffineChannelLaw.affineHash sample w)
                hsample).symm.trans hhash
            · have hpending := (hclear heligible hfull).1
              -- Quota clearing is unconditional on solver success. Its empty
              -- next pending bank contradicts q - 1 > 0 immediately.
              change next.pending = [] at hpending
              rw [hpending, List.length_nil] at hlength
              omega
          · have hbankEq := (hgap heligible).1
            -- A gap preserves both the bank and its full cohort flags. This
            -- yields the same-level prior indicator used by the descent.
            change next = bank at hbankEq
            have hflagsOld := hflagGap heligible
            change nextFlags =
              source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i r w
              at hflagsOld
            refine Or.inl ⟨hqone, hqquota, har, hbirth, ?_⟩
            rw [hprefix]
            refine ⟨?_, ?_, ?_, ?_⟩
            · change bank.completed.length = k
              rw [← hbankEq]
              exact hcompleted
            · change bankBirth a bank = some alpha
              rw [← hbankEq]
              exact hbankBirth
            · change bank.pending.length = q - 1
              rw [← hbankEq]
              exact hlength
            · rw [← hflagsOld]
              exact hgood
  | inr _ =>
      rw [hnextPrefix] at hendpoint
      exact hendpoint.elim

/-- An inactive predecessor cannot create the nonempty active bank required
by a level at least two. The inactive bridge supplies the actual initial state
when activation occurs, including at a block boundary. This statement takes
the literal next indicator, with no assumed reset or activation law. -/
private theorem past_indicator_successor_not_inactive
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star : ℝ)
    (C_h : ℝ)
    (i : Fin (p.m - 1))
    (alpha : ℕ)
    (k : ℕ)
    (q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T)
    (hnext : r.val + 1 < p.T)
    (hq : 2 ≤ q)
    (hI : source_prelaunch_down_past_indicator rate rewards C_star C_h z i
      alpha k q hAlpha ⟨r.val + 1, hnext⟩ w) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inr _) => False
    | _ => True := by
  classical
  let rn : Fin p.T := ⟨r.val + 1, hnext⟩
  cases hprefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl _ => trivial
      | inr inactive =>
          have hendpoint := hI.2.2.2.2
          have hinactive :=
            ReferenceGeneratedPrelaunchDownInactiveBridge.source_prelaunch_down_inactive_successor
              rate rewards C_star C_h z i r hnext
          rw [hprefix] at hinactive
          have hnextData := hinactive.2.2
          cases hnextPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
          | inl nextBranch =>
              cases nextBranch with
              | inl nextActive =>
                  dsimp only [rn] at hnextPrefix
                  rw [hnextPrefix] at hendpoint
                  have hlengthNext := hendpoint.2.2.1
                  rw [hnextPrefix] at hnextData
                  obtain ⟨_, a, _, _, _, _, hinitial, _, _⟩ := hnextData
                  rw [hinitial] at hlengthNext
                  change 0 = q - 1 at hlengthNext
                  omega
              | inr _ =>
                  dsimp only [rn] at hnextPrefix
                  rw [hnextPrefix] at hendpoint
                  exact hendpoint.elim
          | inr _ =>
              dsimp only [rn] at hnextPrefix
              rw [hnextPrefix] at hendpoint
              exact hendpoint.elim
  | inr _ => trivial

/-- Stopped prefixes stay stopped at the next calendar index. The literal
indicator requires an active next prefix, so no stopped predecessor is
possible. This consumes the actual stopped-to-terminal bridge; it does not
discard a stopped branch by imposing a no-stop hypothesis. -/
private theorem past_indicator_successor_not_stopped
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star : ℝ)
    (C_h : ℝ)
    (i : Fin (p.m - 1))
    (alpha : ℕ)
    (k : ℕ)
    (q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T)
    (hnext : r.val + 1 < p.T)
    (hI : source_prelaunch_down_past_indicator rate rewards C_star C_h z i
      alpha k q hAlpha ⟨r.val + 1, hnext⟩ w) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inr _ => False
    | _ => True := by
  classical
  let rn : Fin p.T := ⟨r.val + 1, hnext⟩
  cases hprefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch => cases branch <;> trivial
  | inr stopped =>
      have hstopped :=
        ReferenceGeneratedPrelaunchDownInactiveBridge.source_prelaunch_down_stopped_to_terminal
          rate rewards C_star C_h z i r
      rw [hprefix] at hstopped
      obtain ⟨stoppedNext, hstays, _⟩ :=
        hstopped.2.2.2.2 rn (by dsimp [rn]; omega)
      have hendpoint := hI.2.2.2.2
      dsimp only [rn] at hstays
      rw [hstays] at hendpoint
      exact hendpoint.elim

/-- The complete one-step alternative, after eliminating both non-active
predecessor branches from the actual next indicator. The only additional
inputs are explicit clock bounds and `2 ≤ q`; the public induction supplies
all of them before calling this helper. -/
private theorem past_indicator_successor_cases
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star : ℝ)
    (C_h : ℝ)
    (i : Fin (p.m - 1))
    (alpha : ℕ)
    (k : ℕ)
    (q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T)
    (hnext : r.val + 1 < p.T)
    (har : alpha ≤ r.val)
    (hq : 2 ≤ q)
    (hI : source_prelaunch_down_past_indicator rate rewards C_star C_h z i
      alpha k q hAlpha ⟨r.val + 1, hnext⟩ w) :
    source_prelaunch_down_past_indicator rate rewards C_star C_h z i
        alpha k q hAlpha r w ∨
      prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q - 1)
        hAlpha w z r := by
  cases hprefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          exact past_indicator_successor_of_active rate rewards C_star C_h i alpha k q
            hAlpha w z r hnext har hq active hprefix hI
      | inr inactive =>
          have hfalse := past_indicator_successor_not_inactive rate rewards C_star C_h i
            alpha k q hAlpha w z r hnext hq hI
          rw [hprefix] at hfalse
          exact hfalse.elim
  | inr stopped =>
      have hfalse := past_indicator_successor_not_stopped rate rewards C_star C_h i
        alpha k q hAlpha w z r hnext hI
      rw [hprefix] at hfalse
      exact hfalse.elim

/-- A good nonempty actual pending bank has an earlier hashed occurrence at
the preceding level, in the same fixed birth, ordinal, source point and word.
The current round need not be positive. Both level bounds come from the
literal indicator, apart from the explicit lower bound `2 ≤ q` selecting this
nonempty case. No ancestry or transition-law hypothesis is accepted. -/
theorem past_indicator_exists_previous_hashed_occurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star : ℝ)
    (C_h : ℝ)
    (i : Fin (p.m - 1))
    (alpha : ℕ)
    (k : ℕ)
    (q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T)
    (hq : 2 ≤ q)
    (hI : source_prelaunch_down_past_indicator rate rewards C_star C_h z i
      alpha k q hAlpha r w) :
    ∃ u : Fin p.T, alpha ≤ u.val ∧ u.val < r.val ∧
      prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q - 1)
        hAlpha w z u := by
  have hdescent : ∀ n : ℕ, ∀ t : Fin p.T, t.val = n →
      source_prelaunch_down_past_indicator rate rewards C_star C_h z i
        alpha k q hAlpha t w →
      ∃ u : Fin p.T, alpha ≤ u.val ∧ u.val < t.val ∧
        prelaunchDownHashedOccurrence rate rewards C_star C_h i alpha k (q - 1)
          hAlpha w z u := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t htn hIt
        have hafter := past_indicator_strict_after_birth rate rewards C_star C_h i
          alpha k q hAlpha w z t hq hIt
        have hpredlt : t.val - 1 < p.T := by omega
        let prev : Fin p.T := ⟨t.val - 1, hpredlt⟩
        have hnext : prev.val + 1 < p.T := by
          dsimp [prev]
          omega
        have hnextEq : (⟨prev.val + 1, hnext⟩ : Fin p.T) = t := by
          apply Fin.ext
          dsimp [prev]
          omega
        have hprevBirth : alpha ≤ prev.val := by
          dsimp [prev]
          omega
        have hprevlt : prev.val < t.val := by
          dsimp [prev]
          omega
        have hIatNext : source_prelaunch_down_past_indicator rate rewards C_star C_h z i
            alpha k q hAlpha ⟨prev.val + 1, hnext⟩ w := by
          rw [hnextEq]
          exact hIt
        rcases past_indicator_successor_cases rate rewards C_star C_h i alpha k q
            hAlpha w z prev hnext hprevBirth hq hIatNext with hgap | hhit
        · obtain ⟨u, hborn, hut, hhit⟩ := ih prev.val (by omega) prev rfl hgap
          exact ⟨u, hborn, hut.trans hprevlt, hhit⟩
        · exact ⟨prev, hprevBirth, hprevlt, hhit⟩
  exact hdescent r.val r rfl hI

/-- Every positive-level occurrence belongs to the actual preceding detector.
At level one this consumes the imported birth result; higher levels consume
the earlier actual hashed occurrence produced by the calendar descent. -/
theorem prelaunch_occurrence_previous
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star : ℝ)
    (C_h : ℝ)
    (i : Fin (p.m - 1))
    (alpha : ℕ)
    (k : ℕ)
    (q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : Fin p.T)
    (hq : 1 ≤ q)
    (hOcc : prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r) :
    z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w (q - 1) := by
  by_cases hone : q = 1
  · subst q
    exact prelaunch_occurrence_previous_one rate rewards C_star C_h i alpha k
      hAlpha w z r hOcc
  · have htwo : 2 ≤ q := by omega
    obtain ⟨u, _, _, hhit⟩ := past_indicator_exists_previous_hashed_occurrence
      rate rewards C_star C_h i alpha k q hAlpha w z r htwo hOcc.1
    have hlevel : q - 1 = (q - 2) + 1 := by omega
    rw [hlevel, prelaunchDownDetector_succ]
    exact ⟨u, by simpa only [← hlevel] using hhit⟩

/-- The existence event for an actual occurrence is contained in the actual
preceding detector, for later measure assembly. This is an unconditional
producer of the inclusion from the existing event definitions. -/
theorem prelaunch_occurrence_exists_subset_previous
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star : ℝ)
    (C_h : ℝ)
    (i : Fin (p.m - 1))
    (alpha : ℕ)
    (k : ℕ)
    (q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hq : 1 ≤ q) :
    {z : BootstrapPrivateRoundStreams.SourceInput p | ∃ r : Fin p.T,
      prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r} ⊆
      prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w (q - 1) := by
  rintro z ⟨r, hOcc⟩
  exact prelaunch_occurrence_previous rate rewards C_star C_h i alpha k q
    hAlpha w z r hq hOcc

/-- There is at most one actual occurrence, and any such occurrence forces
the preceding detector. Thus the un-hashed occurrence count is bounded by
the preceding detector indicator. This is a pointwise natural-number bound,
with no probability or caller-supplied inclusion premise. -/
theorem prelaunch_occurrence_indicator_le_previous
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star : ℝ)
    (C_h : ℝ)
    (i : Fin (p.m - 1))
    (alpha : ℕ)
    (k : ℕ)
    (q : ℕ)
    (hAlpha : alpha ≤ p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hq : 1 ≤ q) :
    (∑ r : Fin p.T,
      if prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r
        then (1 : ℕ) else 0) ≤
      if z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w (q - 1)
        then 1 else 0 := by
  classical
  rw [Finset.sum_boole]
  by_cases hdet : z ∈ prelaunchDownDetector rate rewards C_star C_h i alpha k hAlpha w (q - 1)
  · rw [ite_eq_left hdet]
    apply Finset.card_le_one.mpr
    intro r hr s hs
    exact prelaunch_occurrence_unique rate rewards C_star C_h i alpha k q hAlpha w z r s
      (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hs).2
  · rw [ite_eq_right hdet]
    have hempty : (Finset.univ.filter (fun r : Fin p.T =>
        prelaunchDownOccurrence rate rewards C_star C_h i alpha k q hAlpha w z r)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact hdet (prelaunch_occurrence_previous rate rewards C_star C_h i alpha k q
        hAlpha w z r hq (Finset.mem_filter.mp hr).2)
    rw [hempty, Finset.card_empty]
    exact Nat.le_refl 0

end Bandits.Support.ReferenceGeneratedPrelaunchDownOccurrencePredecessor

end
