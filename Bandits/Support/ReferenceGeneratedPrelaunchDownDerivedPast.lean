/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownPrefix

/-!
# Strict-past transport for generated prelaunch DOWN data

Sources: `appendix_a_local_protocol.tex:111-138`,
`appendix_b_communication.tex:724-736`,
`07_public_setup.tex:60-112,127-142`, and
`05_binary_transport.tex:20-42`.

The exports transport only literal test, flag, birth and indicator data under
the original generated strict-past equality. They establish no law or event
bound and do not identify historical births with a later launch bank.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownDerivedPast

open ConstructorDimensions BootstrapDimensions
open ReferenceGeneratedPrelaunchDownPrefix
open ReferenceGeneratedDownBatchCalendar ReferencePrelaunchFollower
open CompleteRowStoppingLaw PrivateRoundFreshness
open ReferenceInitializationRun
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

/-- The branch data retained by the actual prefix projections. Proof fields
and proof-carrying selectors are deliberately omitted from this relation. -/
private def sameSourcePrefixData
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) : Prop :=
  match ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i r,
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z' i r with
  | .inl (.inl a), .inl (.inl b) =>
      a.val.1.val = b.val.1.val ∧ a.val.2.1 = b.val.2.1 ∧
        a.val.2.2.1 = b.val.2.2.1 ∧ a.val.2.2.2 = b.val.2.2.2
  | .inl (.inr a), .inl (.inr b) =>
      a.val.1.val = b.val.1.val ∧ a.val.2 = b.val.2
  | .inr a, .inr b => a.val.1 = b.val.1 ∧ a.val.2 = b.val.2
  | _, _ => False

private theorem sameSourcePrefixData_of_forget_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (h : ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
        (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z i r) =
      ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
        (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r)) :
    sameSourcePrefixData rate rewards C_star C_h z z' i r := by
  cases hleft : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i r with
  | inl left =>
    cases left with
    | inl a =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl b =>
          simp only [sameSourcePrefixData, hleft, hright]
          simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
            hleft, hright] at h
          have hfields :
              a.val.1.val = b.val.1.val ∧ a.val.2.1 = b.val.2.1 ∧
                a.val.2.2.1 = b.val.2.2.1 ∧ a.val.2.2.2 = b.val.2.2.2 := by
            have hinner := Sum.inl.inj h
            have htuple := Sum.inl.inj hinner
            have h1 := congrArg Prod.fst htuple
            have hrest := congrArg Prod.snd htuple
            have h2 := congrArg Prod.fst hrest
            have hrest' := congrArg Prod.snd hrest
            exact ⟨h1, h2, congrArg Prod.fst hrest', congrArg Prod.snd hrest'⟩
          exact hfields
        | inr _ =>
          simp only [sameSourcePrefixData, hleft, hright]
          simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
            hleft, hright] at h
          have hinner := Sum.inl.inj h
          cases hinner
      | inr _ =>
        simp only [sameSourcePrefixData, hleft, hright]
        simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
          hleft, hright] at h
        cases h
    | inr a =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl _ =>
          simp only [sameSourcePrefixData, hleft, hright]
          simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
            hleft, hright] at h
          have hinner := Sum.inl.inj h
          cases hinner
        | inr b =>
          simp only [sameSourcePrefixData, hleft, hright]
          simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
            hleft, hright] at h
          have hinner := Sum.inl.inj h
          have htuple := Sum.inr.inj hinner
          simpa only [Prod.mk.injEq] using htuple
      | inr _ =>
        simp only [sameSourcePrefixData, hleft, hright]
        simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
          hleft, hright] at h
        cases h
  | inr a =>
    cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z' i r with
    | inl right =>
      cases right with
      | inl _ =>
        simp only [sameSourcePrefixData, hleft, hright]
        simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
          hleft, hright] at h
        cases h
      | inr _ =>
        simp only [sameSourcePrefixData, hleft, hright]
        simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
          hleft, hright] at h
        cases h
    | inr b =>
      simp only [sameSourcePrefixData, hleft, hright]
      simp only [ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs,
        hleft, hright] at h
      have hpair := Sum.inr.inj h
      exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- The actual calendar entry of the selected original row at any strict-past
round is reconstructed from the public coordinate of `G.past`. -/
private theorem source_calendar_entry_eq_of_past
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (r t : Fin p.T)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2))
    (ht : t.val < r.val) :
    CompleteRowStoppingLaw.calendarizeRow p
        (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h z).row t =
      CompleteRowStoppingLaw.calendarizeRow p
        (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
          rate rewards C_star C_h z').row t := by
  have hentry := congrArg (fun w : GeneratedBootstrapRoundLaw.Past p r =>
    w.1 ⟨t, ht⟩) hpast
  change CompleteRowStoppingLaw.calendarizeRow p
      (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
        rate rewards C_star C_h z).row t =
    CompleteRowStoppingLaw.calendarizeRow p
      (ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
        rate rewards C_star C_h z').row t at hentry
  exact hentry

/-- The split strict-past private scalar is the original scalar at its retained
player-round label. -/
private theorem extendedPrivateSplit_pastScalar_apply
    (t : Fin p.T)
    (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
    (q : PrivateRoundFreshness.PastRoundLabel p t) :
    ((PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p t e).1).2.1 q =
      e.2.1 q.1.1 := by
  simp [PrivateRoundFreshness.extendedPrivateRoundSplitEquiv,
    PrivateRoundFreshness.playerRoundScalarSplitEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.prodAssoc, Equiv.prodAssoc,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply]

private theorem extendedPrivateSplit_base_apply
    (t : Fin p.T)
    (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    ((PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p t e).1).1 = e.1 := by
  simp [PrivateRoundFreshness.extendedPrivateRoundSplitEquiv,
    PrivateRoundFreshness.playerRoundScalarSplitEquiv,
    MeasurableEquiv.prodAssoc, Equiv.prodAssoc,
    MeasurableEquiv.prodComm, Equiv.prodComm,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply]

private theorem extendedPrivateSplit_target_apply
    (t : Fin p.T)
    (e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    ((PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p t e).1).2.2 =
      e.2.2 := by
  simp [PrivateRoundFreshness.extendedPrivateRoundSplitEquiv,
    PrivateRoundFreshness.playerRoundScalarSplitEquiv,
    MeasurableEquiv.prodAssoc, Equiv.prodAssoc,
    MeasurableEquiv.prodComm, Equiv.prodComm,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply]

/-- Earlier original strict-past coordinates are the restrictions of the
actual split coordinates at `r`, including every retained private scalar. -/
theorem source_generated_past_eq_of_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (u r : Fin p.T) (hur : u.val ≤ r.val)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)) :
    GeneratedBootstrapRoundLaw.past p u
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p u
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2) := by
  let e : GeneratedBootstrapRoundLaw.Coordinates p :=
    (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2)
  let e' : GeneratedBootstrapRoundLaw.Coordinates p :=
    (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)
  have hprivate := congrArg Prod.snd hpast
  change (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r e.2).1 =
    (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p r e'.2).1 at hprivate
  change
    ((CompleteRowStoppingLaw.calendarSplitEquiv p (GeneratedBootstrapRoundLaw.cutoff p u)
      (CompleteRowStoppingLaw.calendarizeRowEquiv p e.1)).1,
      (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p u e.2).1) =
    ((CompleteRowStoppingLaw.calendarSplitEquiv p (GeneratedBootstrapRoundLaw.cutoff p u)
      (CompleteRowStoppingLaw.calendarizeRowEquiv p e'.1)).1,
      (PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p u e'.2).1)
  apply Prod.ext
  · funext q
    have hq : q.1.val < r.val := by
      have hq' := q.2
      change q.1.val < u.val at hq'
      exact Nat.lt_of_lt_of_le hq' hur
    have hentry := congrArg (fun w : GeneratedBootstrapRoundLaw.Past p r =>
      w.1 ⟨q.1, hq⟩) hpast
    change CompleteRowStoppingLaw.calendarizeRow p e.1 q.1 =
      CompleteRowStoppingLaw.calendarizeRow p e'.1 q.1 at hentry
    change CompleteRowStoppingLaw.calendarizeRow p e.1 q.1 =
      CompleteRowStoppingLaw.calendarizeRow p e'.1 q.1
    exact hentry
  · have hbaseRaw := congrArg Prod.fst hprivate
    rw [extendedPrivateSplit_base_apply, extendedPrivateSplit_base_apply] at hbaseRaw
    have hbase :
        ((PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p u e.2).1).1 =
          ((PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p u e'.2).1).1 := by
      rw [extendedPrivateSplit_base_apply, extendedPrivateSplit_base_apply]
      exact hbaseRaw
    have htargetsRaw := congrArg
      (fun w : PrivateRoundFreshness.PastView p r => w.2.2) hprivate
    rw [extendedPrivateSplit_target_apply, extendedPrivateSplit_target_apply] at htargetsRaw
    have htargets :
        ((PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p u e.2).1).2.2 =
          ((PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p u e'.2).1).2.2 := by
      rw [extendedPrivateSplit_target_apply, extendedPrivateSplit_target_apply]
      exact htargetsRaw
    have hscalars :
        ((PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p u e.2).1).2.1 =
          ((PrivateRoundFreshness.extendedPrivateRoundSplitEquiv p u e'.2).1).2.1 := by
      funext q
      let qR : PrivateRoundFreshness.PastRoundLabel p r :=
        ⟨⟨q.1.1, by
            have hq' := q.1.2
            change q.1.1.2.val ≤ u.val at hq'
            exact Nat.le_trans hq' hur⟩,
          by
            have hq' := q.2
            change q.1.1.2.val < u.val at hq'
            exact Nat.lt_of_lt_of_le hq' hur⟩
      have hqR := congrArg
        (fun w : PrivateRoundFreshness.PastView p r => w.2.1 qR) hprivate
      have hraw : e.2.2.1 q.1.1 = e'.2.2.1 q.1.1 := by
        rw [extendedPrivateSplit_pastScalar_apply,
          extendedPrivateSplit_pastScalar_apply] at hqR
        simpa only [qR] using hqR
      rw [extendedPrivateSplit_pastScalar_apply,
        extendedPrivateSplit_pastScalar_apply]
      exact hraw
    exact Prod.ext hbase (Prod.ext hscalars htargets)

private theorem active_prelaunch_tests_eq
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (x y : ReferenceInitializationRun.Input p)
    (a a' : ReferencePrelaunchFollower.Activation p)
    (history history' : ReferencePrelaunchFollower.LocalHistory p r.val)
    (ha : a = a') (hhistory : history = history')
    (hrow : ∀ u : Fin r.val,
      CompleteRowStoppingLaw.calendarizeRow p x.row
          (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u) =
        CompleteRowStoppingLaw.calendarizeRow p y.row
          (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u)) :
    ((List.ofFn fun u : Fin r.val => u).filterMap fun u =>
      ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i x.row a
        (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u) (history u)) =
    ((List.ofFn fun u : Fin r.val => u).filterMap fun u =>
      ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i y.row a'
        (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u) (history' u)) := by
  cases ha
  cases hhistory
  apply List.filterMap_congr
  intro u _
  let t := ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u
  have hentry := hrow u
  change (fun j => x.row.1 j t, x.row.2 t) =
    (fun j => y.row.1 j t, y.row.2 t) at hentry
  have hcontrol : x.row.2 t = y.row.2 t := congrArg Prod.snd hentry
  have hselected :
      (ReferencePrelaunchFollower.downInput i x.row a t (history u)).selected =
        (ReferencePrelaunchFollower.downInput i y.row a t (history u)).selected := by
    simp [ReferencePrelaunchFollower.downInput, hcontrol]
  have hsample :
      (ReferencePrelaunchFollower.downInput i x.row a t (history u)).sample =
        (ReferencePrelaunchFollower.downInput i y.row a t (history u)).sample := by
    simp [ReferencePrelaunchFollower.downInput, hcontrol] <;> rfl
  simp only [t, ReferenceGeneratedPrelaunchDownCohort.prelaunchTest, hselected, hsample]

private theorem stopped_prelaunch_tests_eq
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (x y : ReferenceInitializationRun.Input p)
    (b b' : ReferenceInitializationRun.Boundary p)
    (hb : b = b')
    (hrow : ∀ t : Fin p.T,
      t.val < ReferenceInitializationRun.elapsed p b.completed →
      CompleteRowStoppingLaw.calendarizeRow p x.row t =
        CompleteRowStoppingLaw.calendarizeRow p y.row t) :
    ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests x b i =
      ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests y b' i := by
  cases hb
  unfold ReferenceGeneratedPrelaunchDownCohort.boundaryPrelaunchDownTests
  cases hforced : b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) with
  | true => simp [hforced]
  | false =>
    cases hactivation : b.activation (ActualReferenceInitializationBlock.refFollower i) with
    | none => simp [hforced, hactivation]
    | some a =>
      simp only [hforced, hactivation]
      apply List.filterMap_congr
      intro u _
      let t := ReferencePrelaunchFollower.calendar
        (ReferenceInitializationRun.elapsed_le_T p b.completed) u
      have hentry := hrow t (by
        change u.val < ReferenceInitializationRun.elapsed p b.completed
        exact u.isLt)
      change (fun j => x.row.1 j t, x.row.2 t) =
        (fun j => y.row.1 j t, y.row.2 t) at hentry
      have hcontrol : x.row.2 t = y.row.2 t := congrArg Prod.snd hentry
      have hselected :
          (ReferencePrelaunchFollower.downInput i x.row a t
            (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) u)).selected =
            (ReferencePrelaunchFollower.downInput i y.row a t
              (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ActualReferenceInitializationBlock.refFollower i)) u)).selected := by
        simp [ReferencePrelaunchFollower.downInput, hcontrol]
      have hsample :
          (ReferencePrelaunchFollower.downInput i x.row a t
            (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) u)).sample =
            (ReferencePrelaunchFollower.downInput i y.row a t
              (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ActualReferenceInitializationBlock.refFollower i)) u)).sample := by
        simp [ReferencePrelaunchFollower.downInput, hcontrol] <;> rfl
      simp only [t, ReferenceGeneratedPrelaunchDownCohort.prelaunchTest, hselected, hsample]

private theorem prefix_prelaunch_birth_eq_of_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (hdata : sameSourcePrefixData rate rewards C_star C_h z z' i r) :
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth
        rate rewards C_star C_h z i r =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth
        rate rewards C_star C_h z' i r := by
  cases hleft : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i r with
  | inl left =>
    cases left with
    | inl leftActive =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl rightActive =>
          simp only [hleft, hright, sameSourcePrefixData] at hdata
          rcases hdata with ⟨_, ha, _, hs⟩
          simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth,
            hleft, hright]
          rw [ha, hs]
        | inr _ =>
          simp only [hleft, hright, sameSourcePrefixData] at hdata
      | inr _ =>
        simp only [hleft, hright, sameSourcePrefixData] at hdata
    | inr _ =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
        | inr _ =>
          simp only [hleft, hright,
            ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth]
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
  | inr leftStopped =>
    cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z' i r with
    | inl right =>
      cases right with
      | inl _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
    | inr rightStopped =>
      simp only [hleft, hright, sameSourcePrefixData] at hdata
      rcases hdata with ⟨hb, hs⟩
      simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth,
        hleft, hright]
      rw [hb, hs]

/-- The current pending-cohort flags use exactly the actual prefix tests and
the completed length of the current literal DOWN bank. -/
private theorem current_cohort_flags_eq_of_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hdata : sameSourcePrefixData rate rewards C_star C_h z z' i r)
    (hflags : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_flags
        rate rewards C_star C_h z i r w =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_flags
        rate rewards C_star C_h z' i r w) :
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags
        rate rewards C_star C_h z i r w =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags
        rate rewards C_star C_h z' i r w := by
  cases hleft : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i r with
  | inl left =>
    cases left with
    | inl leftActive =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl rightActive =>
          simp only [hleft, hright, sameSourcePrefixData] at hdata
          rcases hdata with ⟨_, _, _, hs⟩
          simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags,
            hleft, hright]
          rw [hflags, hs]
        | inr _ =>
          simp only [hleft, hright, sameSourcePrefixData] at hdata
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
    | inr _ =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
        | inr _ =>
          simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags,
            hleft, hright]
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
  | inr leftStopped =>
    cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z' i r with
    | inl right =>
      cases right with
      | inl _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
    | inr rightStopped =>
      simp only [hleft, hright, sameSourcePrefixData] at hdata
      rcases hdata with ⟨_, hs⟩
      simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags,
        hleft, hright]
      rw [hflags, hs]

/-- With the corresponding earlier birth and current cohort flags aligned,
the literal past indicator is transported by the same actual prefix branch. -/
private theorem past_indicator_iff_of_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (alpha k ell : ℕ) (hα : alpha ≤ p.T)
    (r : Fin p.T) (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hbirth : ReferenceGeneratedPrelaunchDownPrefix.birthAt
        rate rewards C_star C_h z i alpha hα k ↔
      ReferenceGeneratedPrelaunchDownPrefix.birthAt
        rate rewards C_star C_h z' i alpha hα k)
    (hcohort : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags
        rate rewards C_star C_h z i r w =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags
        rate rewards C_star C_h z' i r w)
    (hdata : sameSourcePrefixData rate rewards C_star C_h z z' i r) :
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
        rate rewards C_star C_h z i alpha k ell hα r w ↔
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
        rate rewards C_star C_h z' i alpha k ell hα r w := by
  cases hleft : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i r with
  | inl left =>
    cases left with
    | inl leftActive =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl rightActive =>
          simp only [hleft, hright, sameSourcePrefixData] at hdata
          rcases hdata with ⟨_, ha, _, hs⟩
          simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator,
            hleft, hright]
          rw [hbirth, ha, hs, hcohort]
        | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
    | inr _ =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
        | inr _ =>
          simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator,
            hleft, hright]
          rw [hbirth]
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
  | inr leftStopped =>
    cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z' i r with
    | inl right =>
      cases right with
      | inl _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
    | inr rightStopped =>
      simp [hleft, hright,
        ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator]

/-- The generated original-row test list is equal under the actual strict-past
condition. Each test keeps its original sample, time, and sent-word field. -/
theorem source_prelaunch_down_prefix_tests_eq_of_past
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)) :
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
        rate rewards C_star C_h z i r =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests
        rate rewards C_star C_h z' i r := by
  let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
    rate rewards C_star C_h z
  let y := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
    rate rewards C_star C_h z'
  have hobs := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_past_invariant
    rate rewards C_star C_h z z' i r hids hpast
  have hobs' :
      ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z i r) =
        ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z' i r) := by
    simpa only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
      using hobs
  have hdata := sameSourcePrefixData_of_forget_eq rate rewards C_star C_h z z' i r hobs'
  have hrow : ∀ u : Fin r.val,
      CompleteRowStoppingLaw.calendarizeRow p x.row
          (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u) =
        CompleteRowStoppingLaw.calendarizeRow p y.row
          (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u) := by
    intro u
    exact source_calendar_entry_eq_of_past rate rewards C_star C_h z z' r
      (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) u) hpast u.isLt
  cases hleft : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i r with
  | inl left =>
    cases left with
    | inl a =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl b =>
          simp only [hleft, hright, sameSourcePrefixData] at hdata
          rcases hdata with ⟨_, ha, hh, _⟩
          simpa only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests,
            hleft, hright] using active_prelaunch_tests_eq i r x y a.val.2.1 b.val.2.1
              a.val.2.2.1 b.val.2.2.1 ha hh hrow
        | inr _ =>
          simp_all only [hleft, hright, sameSourcePrefixData]
      | inr _ =>
        simp_all only [hleft, hright, sameSourcePrefixData]
    | inr _ =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i r with
      | inl right =>
        cases right with
        | inl _ =>
          simp_all only [hleft, hright, sameSourcePrefixData]
        | inr _ =>
          simp only [hleft, hright, sameSourcePrefixData] at hdata
          simp only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests,
            hleft, hright]
      | inr _ =>
        simp_all only [hleft, hright, sameSourcePrefixData]
  | inr a =>
    cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z' i r with
    | inl right =>
      cases right with
      | inl _ => simp_all only [hleft, hright, sameSourcePrefixData]
      | inr _ => simp_all only [hleft, hright, sameSourcePrefixData]
    | inr b =>
      simp only [hleft, hright, sameSourcePrefixData] at hdata
      rcases hdata with ⟨hb, _⟩
      let x' := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
        rate rewards C_star C_h z
      let y' := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
        rate rewards C_star C_h z'
      have hcompleted : a.val.1.completed ≤ (roundBlockIndex p r).val := by
        rw [a.property.2.1]
        exact ReferenceInitializationPrefixInvariance.run_completed_le x'
          (roundBlockIndex p r).val
      have hstart : ReferenceInitializationRun.elapsed p (roundBlockIndex p r).val ≤ r.val :=
        GeneratedBootstrapRoundLaw.elapsed_le_of_mem_calendarBlock
          (s := roundBlockIndex p r) (t := r)
          (round_mem_quotient_block p r)
      have helapsed : ReferenceInitializationRun.elapsed p a.val.1.completed ≤ r.val :=
        (ReferenceInitializationRun.elapsed_mono p hcompleted).trans hstart
      have hrowStopped : ∀ t : Fin p.T,
          t.val < ReferenceInitializationRun.elapsed p a.val.1.completed →
          CompleteRowStoppingLaw.calendarizeRow p x'.row t =
            CompleteRowStoppingLaw.calendarizeRow p y'.row t := by
        intro t ht
        exact source_calendar_entry_eq_of_past rate rewards C_star C_h z z' r t
          hpast (lt_of_lt_of_le ht helapsed)
      simpa only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_tests,
        hleft, hright] using stopped_prelaunch_tests_eq i r x' y' a.val.1 b.val.1 hb
          hrowStopped

/-- Sent-word and affine-hash flags are mapped from the complete actual tests. -/
theorem source_prelaunch_down_prefix_flags_eq_of_past
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2))
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_flags
        rate rewards C_star C_h z i r w =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_flags
        rate rewards C_star C_h z' i r w := by
  unfold ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_flags
  rw [source_prelaunch_down_prefix_tests_eq_of_past
    rate rewards C_star C_h z z' i r hids hpast]

/-- The actual pending-cohort flags agree, including the drop determined by
the actual completed DOWN batches on active and stopped branches. -/
theorem source_prelaunch_down_current_cohort_flags_eq_of_past
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2))
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags
        rate rewards C_star C_h z i r w =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_current_cohort_flags
        rate rewards C_star C_h z' i r w := by
  have hobs := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_past_invariant
    rate rewards C_star C_h z z' i r hids hpast
  have hobs' :
      ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z i r) =
        ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z' i r) := by
    simpa only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
      using hobs
  have hdata := sameSourcePrefixData_of_forget_eq rate rewards C_star C_h z z' i r hobs'
  exact current_cohort_flags_eq_of_data rate rewards C_star C_h z z' i r w hdata
    (source_prelaunch_down_prefix_flags_eq_of_past
      rate rewards C_star C_h z z' i r hids hpast w)

/-- The literal prefix birth projection agrees under the actual strict-past
condition. This does not characterize historical birth by a launch event. -/
theorem source_prelaunch_down_prefix_birth_eq_of_past
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)) :
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth
        rate rewards C_star C_h z i r =
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_birth
        rate rewards C_star C_h z' i r := by
  have hobs := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_past_invariant
    rate rewards C_star C_h z z' i r hids hpast
  have hobs' :
      ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z i r) =
        ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z' i r) := by
    simpa only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
      using hobs
  exact prefix_prelaunch_birth_eq_of_data rate rewards C_star C_h z z' i r
    (sameSourcePrefixData_of_forget_eq rate rewards C_star C_h z z' i r hobs')

private theorem birthAt_iff_of_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (k : ℕ)
    (hdata : sameSourcePrefixData rate rewards C_star C_h z z' i t) :
    ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h z i
        t.val (Nat.le_of_lt t.isLt) k ↔
      ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h z' i
        t.val (Nat.le_of_lt t.isLt) k := by
  cases hleft : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h z i t with
  | inl left =>
    cases left with
    | inl leftActive =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i t with
      | inl right =>
        cases right with
        | inl rightActive =>
          simp only [hleft, hright, sameSourcePrefixData] at hdata
          rcases hdata with ⟨_, ha, _, hs⟩
          simp only [ReferenceGeneratedPrelaunchDownPrefix.birthAt,
            dif_pos t.isLt, hleft, hright]
          rw [ha, hs]
        | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
    | inr _ =>
      cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
          rate rewards C_star C_h z' i t with
      | inl right =>
        cases right with
        | inl _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
        | inr _ =>
          simp only [ReferenceGeneratedPrelaunchDownPrefix.birthAt,
            dif_pos t.isLt, hleft, hright]
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
  | inr leftStopped =>
    cases hright : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
        rate rewards C_star C_h z' i t with
    | inl right =>
      cases right with
      | inl _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
      | inr _ => simp only [hleft, hright, sameSourcePrefixData] at hdata
    | inr rightStopped =>
      simp only [hleft, hright, sameSourcePrefixData] at hdata
      rcases hdata with ⟨hb, hs⟩
      simp only [ReferenceGeneratedPrelaunchDownPrefix.birthAt,
        dif_pos t.isLt, hleft, hright]
      rw [hb, hs]

/-- The existing literal `birthAt` predicate is strict-past invariant at every
`alpha ≤ r`; here `alpha < T` follows from the actual finite round `r`. -/
theorem source_prelaunch_down_birthAt_iff_of_past
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (hα : alpha ≤ p.T) (k : ℕ)
    (r : Fin p.T) (hαr : alpha ≤ r.val)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2)) :
    ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h z i alpha hα k ↔
      ReferenceGeneratedPrelaunchDownPrefix.birthAt rate rewards C_star C_h z' i alpha hα k := by
  have hαT : alpha < p.T := lt_of_le_of_lt hαr r.isLt
  let u : Fin p.T := ⟨alpha, hαT⟩
  have hur : u.val ≤ r.val := by simpa only [u] using hαr
  have hpastU := source_generated_past_eq_of_le
    rate rewards C_star C_h z z' u r hur hpast
  have hobsU := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_past_invariant
    rate rewards C_star C_h z z' i u hids hpastU
  have hobsU' :
      ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z i u) =
        ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
          (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
            rate rewards C_star C_h z' i u) := by
    simpa only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
      using hobsU
  have hdataU := sameSourcePrefixData_of_forget_eq rate rewards C_star C_h z z' i u hobsU'
  have hbirthU := birthAt_iff_of_data rate rewards C_star C_h z z' i u k hdataU
  simpa only [u] using hbirthU

/-- The actual literal strict-past indicator is invariant under the original
source-past equality. For `alpha > r.val` both indicators reduce to false. -/
theorem source_prelaunch_down_past_indicator_iff_of_past
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z z' : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (alpha k ell : ℕ) (hα : alpha ≤ p.T)
    (r : Fin p.T)
    (hids : z.1.1 = z'.1.1)
    (hpast : GeneratedBootstrapRoundLaw.past p r
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z), z.2) =
      GeneratedBootstrapRoundLaw.past p r
        (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z'), z'.2))
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
        rate rewards C_star C_h z i alpha k ell hα r w ↔
      ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator
        rate rewards C_star C_h z' i alpha k ell hα r w := by
  by_cases hαr : alpha ≤ r.val
  · have hobs := ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_past_invariant
      rate rewards C_star C_h z z' i r hids hpast
    have hobs' :
        ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
            (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
              rate rewards C_star C_h z i r) =
          ReferenceGeneratedPrelaunchDownPrefix.forgetPrefixProofs
            (ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
              rate rewards C_star C_h z' i r) := by
      simpa only [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix_observation, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
        using hobs
    have hdata := sameSourcePrefixData_of_forget_eq rate rewards C_star C_h z z' i r hobs'
    have hcohort := source_prelaunch_down_current_cohort_flags_eq_of_past
      rate rewards C_star C_h z z' i r hids hpast w
    have hαT : alpha < p.T := lt_of_le_of_lt hαr r.isLt
    let u : Fin p.T := ⟨alpha, hαT⟩
    have hur : u.val ≤ r.val := by simpa only [u] using hαr
    have hpastU := source_generated_past_eq_of_le
      rate rewards C_star C_h z z' u r hur hpast
    have hbirth := source_prelaunch_down_birthAt_iff_of_past
      rate rewards C_star C_h z z' i alpha hα k u (by rfl) hids hpastU
    exact past_indicator_iff_of_data rate rewards C_star C_h z z' i alpha k ell hα r w
      hbirth hcohort hdata
  · simp [ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_past_indicator, hαr]

end Bandits.Support.ReferenceGeneratedPrelaunchDownDerivedPast
