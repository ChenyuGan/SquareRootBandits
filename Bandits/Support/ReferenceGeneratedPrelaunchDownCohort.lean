/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownBatchCalendar
public import Bandits.Support.ReferencePrelaunchDownInvariance
public import Bandits.Support.ReferencePrelaunchCarriedMeasurability

/-!
# Generated prelaunch DOWN cohorts

Deterministic internal support for `07_public_setup.tex:60-112,127-142`,
`05_binary_transport.tex:20-42`, `appendix_a_local_protocol.tex:92-119`, and
`appendix_b_communication.tex:724-736`. The tests below project the existing
ordinary replay of the generated physical history. The source input retains
all rows, IDs, J, private arrays, rewards and unrestricted shared constants.

Physical provenance is established separately from equation storage. No
probability, conditional tail, source event coverage or regret claim is made.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownCohort

open ConstructorDimensions BootstrapDimensions ActiveRoundActions
open scoped Classical

variable {p : Parameters}

/-- Forget only the sent-word annotation, retaining the existing stamped entry. -/
def testEntry (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :
    AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) :=
  ⟨test.time, test.sample⟩

/-- One selected positive in the canonical replay. This is a projection, not
an additional receiver or transition. Physical absence is proved below. -/
def prelaunchTest (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (a : ReferencePrelaunchFollower.Activation p) (t : Fin p.T) (own : Fin p.K × ReferencePrelaunchFollower.Observation p) :
    Option (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :=
  if (ReferencePrelaunchFollower.downInput i row a t own).selected = true ∧ 0 < own.2.val.val then
    some ⟨t, (ReferencePrelaunchFollower.downInput i row a t own).sample, none⟩
  else none

/-- Literal census of the existing ordinary projection at any boundary.
Forced initialization discards the replay bank, as does the existing `ordinary`. -/
def boundaryPrelaunchDownTests (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (i : Fin (p.m - 1)) : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :=
  let f := ActualReferenceInitializationBlock.refFollower i
  if b.forcedFailure f then [] else
    match b.activation f with
    | none => []
    | some a => (List.ofFn (fun u : Fin (ReferenceInitializationRun.elapsed p b.completed) => u)).filterMap
        (fun u => prelaunchTest i x.row a
          (ReferencePrelaunchFollower.calendar (ReferenceInitializationRun.elapsed_le_T p b.completed) u)
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f) u))

/-- The requested census, computed from the original whole source. -/
def sourcePrelaunchDownTests (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) :
    List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :=
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  boundaryPrelaunchDownTests x (ReferenceInitializationRun.output x) i

private theorem prelaunchTest_entries (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (a : ReferencePrelaunchFollower.Activation p)
    (t : Fin p.T) (own : Fin p.K × ReferencePrelaunchFollower.Observation p) :
    ((prelaunchTest i row a t own).toList.map testEntry) =
      AffineBatchDecoder.positiveAt p (ReferencePrelaunchFollower.traceAt i row a t own) t := by
  by_cases h : (ReferencePrelaunchFollower.downInput i row a t own).selected = true ∧ 0 < own.2.val.val
  · have he : AffineBatchDecoder.eligible (ReferencePrelaunchFollower.traceAt i row a t own t) := ⟨h.1, rfl, h.2⟩
    rw [prelaunchTest, ite_eq_left h, AffineBatchDecoder.positiveAt, ite_eq_left he]
    rfl
  · have he : ¬ AffineBatchDecoder.eligible (ReferencePrelaunchFollower.traceAt i row a t own t) := fun he => h ⟨he.1, he.2.2⟩
    simp only [prelaunchTest, h, ↓reduceIte, Option.toList_none, List.map_nil,
      AffineBatchDecoder.positiveAt, he]

private theorem tests_entries (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (a : ReferencePrelaunchFollower.Activation p)
    {n : ℕ} (history : ReferencePrelaunchFollower.LocalHistory p n) (hn : n ≤ p.T) (us : List (Fin n)) :
    (us.filterMap (fun u => prelaunchTest i row a (ReferencePrelaunchFollower.calendar hn u) (history u))).map
      testEntry = us.flatMap (fun u => AffineBatchDecoder.positiveAt p
        (ReferencePrelaunchFollower.traceAt i row a (ReferencePrelaunchFollower.calendar hn u)
          (history u)) (ReferencePrelaunchFollower.calendar hn u)) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    rw [List.filterMap_cons, List.flatMap_cons]
    cases h : prelaunchTest i row a (ReferencePrelaunchFollower.calendar hn u) (history u) with
    | none =>
      have he := prelaunchTest_entries i row a (ReferencePrelaunchFollower.calendar hn u) (history u)
      simp only [h, Option.toList_none, List.map_nil] at he
      simp only [ih, ← he, List.nil_append]
    | some test =>
      have he := prelaunchTest_entries i row a (ReferencePrelaunchFollower.calendar hn u) (history u)
      simp only [h, Option.toList_some, List.map_cons, List.map_nil] at he
      simp only [List.map_cons, ih, ← he, List.singleton_append]

private theorem boundary_census (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (i : Fin (p.m - 1)) :
    let bank := (ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i)).downBatch
    (boundaryPrelaunchDownTests x b i).map testEntry = AffineBatchDecoder.collected bank ∧
      bank.pending.length < AffineBatchDecoder.quota p ∧
      ∀ batch ∈ bank.completed, batch.length = AffineBatchDecoder.quota p := by
  dsimp only
  dsimp only [boundaryPrelaunchDownTests]
  unfold ReferenceInitializationRun.ordinary
  split_ifs with hf
  · exact ⟨rfl, AffineBatchDecoder.quota_pos p, by
      simp only [ReferencePrelaunchFollower.forcedAtLaunch, ReferencePrelaunchFollower.initial,
      AffineBatchDecoder.initial, List.not_mem_nil, false_implies, implies_true]⟩
  · cases ha : b.activation (ActualReferenceInitializationBlock.refFollower i) with
    | none => exact ⟨rfl, AffineBatchDecoder.quota_pos p, by
        simp only [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial,
        List.not_mem_nil, false_implies, implies_true]⟩
    | some a =>
      have hs := ReferencePrelaunchFollower.replay_batch_spec x.eta i x.row a
        (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i))) (ReferenceInitializationRun.elapsed_le_T p b.completed)
      refine ⟨?_, hs.1, hs.2.1⟩
      exact (tests_entries i x.row a _ _ _).trans hs.2.2.symm

private theorem completed_slice (batches : List (List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))))
    (pending : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hall : ∀ batch ∈ batches, batch.length = AffineBatchDecoder.quota p) :
    (batches.flatten ++ pending).drop (AffineBatchDecoder.quota p * batches.length) = pending ∧
      ∀ k (hk : k < batches.length),
        ((batches.flatten ++ pending).drop (k * AffineBatchDecoder.quota p)).take (AffineBatchDecoder.quota p) =
          batches[k] := by
  induction batches with
  | nil => exact ⟨rfl, fun k hk => (Nat.not_lt_zero k hk).elim⟩
  | cons batch batches ih =>
    have hb := hall batch (List.mem_cons_self)
    have ht := ih (fun c hc => hall c (List.mem_cons_of_mem _ hc))
    constructor
    · rw [List.length_cons, Nat.mul_succ, Nat.add_comm,
        List.flatten_cons, List.append_assoc, ← hb, ← List.drop_drop,
        List.drop_left, hb]
      exact ht.1
    · intro k hk
      cases k with
      | zero =>
        simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons,
          List.append_assoc, List.getElem_cons_zero]
        rw [← hb, List.take_left]
      | succ k =>
        simp only [List.length_cons] at hk
        rw [Nat.succ_mul, Nat.add_comm, List.flatten_cons, List.append_assoc,
          ← hb, ← List.drop_drop, List.drop_left, hb, List.getElem_cons_succ]
        exact ht.2 k (by omega)

/-- Exact collection and quota partition, including terminal no-crossing runs.
There is no successful-decision, ordinary-endpoint or activation premise. -/
theorem source_prelaunch_down_cohorts (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let bank := (ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i)).downBatch
    let W := (sourcePrelaunchDownTests rate rewards C_star C_h z i).map testEntry
    W = AffineBatchDecoder.collected bank ∧ bank.pending = W.drop (AffineBatchDecoder.quota p * bank.completed.length) ∧
      (∀ k (hk : k < bank.completed.length),
        bank.completed[k] = (W.drop (k * AffineBatchDecoder.quota p)).take (AffineBatchDecoder.quota p) ∧
        bank.completed[k].length = AffineBatchDecoder.quota p) ∧
      bank.pending.length < AffineBatchDecoder.quota p := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  obtain ⟨hw, hp, hc⟩ := boundary_census x b i
  have hslice := completed_slice
    (ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed
    (ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i)).downBatch.pending hc
  refine ⟨hw, ?_, ?_, hp⟩
  · rw [show sourcePrelaunchDownTests rate rewards C_star C_h z i =
      boundaryPrelaunchDownTests x b i from rfl, hw]
    exact hslice.1.symm
  · intro k hk
    refine ⟨?_, hc _ (List.getElem_mem hk)⟩
    rw [show sourcePrelaunchDownTests rate rewards C_star C_h z i =
      boundaryPrelaunchDownTests x b i from rfl, hw]
    exact (hslice.2 k hk).symm

private theorem activation_before_finish (x : ReferenceInitializationRun.Input p) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p) (f : Follower p.m) (a : ReferencePrelaunchFollower.Activation p)
    (ha : (ReferenceInitializationRun.finishBlock x b h).activation f = some a)
    (he : a.val ≤ ReferenceInitializationRun.elapsed p (b.completed + 1)) : b.activation f = some a := by
  cases hp : b.activation f with
  | some old =>
    have hsame := ReferenceInitializationRun.activated_activation x b h f old hp
    rw [hsame] at ha
    exact ha
  | none =>
    have hi : f ∈ ReferenceInitializationRun.uninformed b := (ReferenceInitializationRun.mem_uninformed b f).2 hp
    change ReferenceInitializationRun.finalActivation x b h f = some a at ha
    unfold ReferenceInitializationRun.finalActivation at ha
    split_ifs at ha with hf
    · have heq := Option.some.inj ha
      have hev := congrArg Subtype.val heq
      dsimp only [ReferenceInitializationRun.boundaryActivation] at hev
      omega
    · simp only [ReferenceInitializationRun.declaredActivation, dite_eq_left hi] at ha
      split_ifs at ha with hs
      · have heq := Option.some.inj ha
        have hev := congrArg Subtype.val heq
        dsimp only [ReferenceInitializationRun.boundaryActivation] at hev
        omega

/-- Every active observation in a generated prefix belongs to its very same
physical block. The predecessor boundary and activation are produced by the
stopped-run induction, including the block that first crosses. -/
theorem run_active_history_origin (x : ReferenceInitializationRun.Input p) (r : ℕ) (f : Follower p.m)
    (a : ReferencePrelaunchFollower.Activation p) (ha : (ReferenceInitializationRun.run x r).activation f = some a)
    (t : Fin p.T) (ht : t.val < ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.run x r).completed)
    (hactive : a.val ≤ t.val + 1) :
    ∃ q, ∃ h : (ReferenceInitializationRun.run x q).completed < n_boot p,
      (ReferenceInitializationRun.run x q).crossing = none ∧ (ReferenceInitializationRun.run x q).activation f = some a ∧
      ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.run x q).completed ≤ t.val ∧
      t.val < ReferenceInitializationRun.elapsed p ((ReferenceInitializationRun.run x q).completed + 1) ∧
      ∃ u : Fin (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.run x r).completed),
      u.val = t.val ∧
      (ReferenceInitializationRun.run x r).history (PublicDiscreteDraws.followerPlayer p.two_le_m f) u =
        ReferenceInitializationRun.ownEntry (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
          (PublicDiscreteDraws.followerPlayer p.two_le_m f) t := by
  induction r with
  | zero =>
    have ha0 : none = some a := ha
    cases ha0
  | succ r ih =>
    by_cases hc : (ReferenceInitializationRun.run x r).crossing.isSome = true
    · rw [ReferenceInitializationRun.run_succ,
        ReferenceInitializationRun.advance_of_crossing x _ hc] at ha ht ⊢
      exact ih ha ht
    · have hn : (ReferenceInitializationRun.run x r).crossing = none := by
        cases hh : (ReferenceInitializationRun.run x r).crossing <;>
          simp_all only [Option.isSome_some, not_true_eq_false]
      by_cases h : (ReferenceInitializationRun.run x r).completed < n_boot p
      · rw [ReferenceInitializationRun.run_succ,
          ReferenceInitializationRun.advance_of_no_crossing x _ hn h] at ha ht ⊢
        have ha' := activation_before_finish x (ReferenceInitializationRun.run x r) h f a ha
          (by simpa only [ReferenceInitializationRun.finishBlock] using (by omega :
            a.val ≤ ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r) h).completed))
        by_cases hp : t.val < ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.run x r).completed
        · obtain ⟨q, hq, hnone, hactivation, hstart, hend, u, hu, hown⟩ := ih ha' hp
          refine ⟨q, hq, hnone, hactivation, hstart, hend,
            ⟨t.val, ht⟩, rfl, ?_⟩
          change (ReferenceInitializationRun.extendedHistory x (ReferenceInitializationRun.run x r) h
            (PublicDiscreteDraws.followerPlayer p.two_le_m f) _) = _
          simp only [ReferenceInitializationRun.extendedHistory, dite_eq_left hp]
          have huEq : u = ⟨t.val, hp⟩ := Fin.ext hu
          rw [huEq] at hown
          exact hown
        · refine ⟨r, h, hn, ha', Nat.le_of_not_gt hp, ht,
            ⟨t.val, ht⟩, rfl, ?_⟩
          change (ReferenceInitializationRun.extendedHistory x (ReferenceInitializationRun.run x r) h
            (PublicDiscreteDraws.followerPlayer p.two_le_m f) _) = _
          simp only [ReferenceInitializationRun.extendedHistory, dite_eq_right hp]
      · rw [ReferenceInitializationRun.run_succ,
          ReferenceInitializationRun.advance_of_exhausted x _ (Nat.le_of_not_gt h)] at ha ht ⊢
        exact ih ha ht

private theorem prelaunchTest_eq_some_iff (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (a : ReferencePrelaunchFollower.Activation p)
    (t : Fin p.T) (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :
    prelaunchTest i row a t own = some test ↔
      (ReferencePrelaunchFollower.downInput i row a t own).selected = true ∧
      0 < own.2.val.val ∧ test = ⟨t, (row.2 t).2 (0, i), none⟩ := by
  unfold prelaunchTest
  split_ifs with h
  · rw [Option.some.injEq]
    exact ⟨fun he => ⟨h.1, h.2, he.symm⟩, fun he => he.2.2.symm⟩
  · constructor
    · intro he; cases he
    · intro he; exact (h ⟨he.1, he.2.1⟩).elim

/-- The converse census: every selected positive of the canonical ordinary
replay is present. Forced and undeclared projections have no tests. -/
theorem mem_boundaryPrelaunchDownTests_iff (x : ReferenceInitializationRun.Input p)
    (b : ReferenceInitializationRun.Boundary p) (i : Fin (p.m - 1))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :
    test ∈ boundaryPrelaunchDownTests x b i ↔
      b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = false ∧
      ∃ a, b.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
        ∃ u : Fin (ReferenceInitializationRun.elapsed p b.completed),
          (ReferencePrelaunchFollower.downInput i x.row a
            (ReferencePrelaunchFollower.calendar
              (ReferenceInitializationRun.elapsed_le_T p b.completed) u)
            (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) u)).selected = true ∧
          0 < (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) u).2.val.val ∧
          test = ⟨ReferencePrelaunchFollower.calendar
            (ReferenceInitializationRun.elapsed_le_T p b.completed) u,
            (x.row.2 (ReferencePrelaunchFollower.calendar
              (ReferenceInitializationRun.elapsed_le_T p b.completed) u)).2 (0, i), none⟩ := by
  cases hf : b.forcedFailure (ActualReferenceInitializationBlock.refFollower i)
  · cases ha : b.activation (ActualReferenceInitializationBlock.refFollower i) <;>
      simp only [boundaryPrelaunchDownTests, hf, Bool.false_eq_true, ↓reduceIte,
        ha, List.not_mem_nil, true_and, Option.some.injEq, reduceCtorEq,
        exists_false, false_and, List.mem_filterMap, List.mem_ofFn, exists_eq,
        prelaunchTest_eq_some_iff, exists_eq_left']
  · simp only [boundaryPrelaunchDownTests, hf, ↓reduceIte, List.not_mem_nil,
      Bool.true_eq_false, false_and]

/-- Each retained positive has its original private sample and generated
physical observation. The actual coordinator has no ordinary learner and
plays the bootstrap DOWN tuple arm; absence of a word is not inferred from
the entry type or from independence of the affine map. -/
theorem source_prelaunch_down_test_provenance
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (hmem : test ∈ sourcePrelaunchDownTests rate rewards C_star C_h z i) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let f := ActualReferenceInitializationBlock.refFollower i
    ∃ a, b.activation f = some a ∧ a.val ≤ test.time.val + 1 ∧
      test.time.val < ReferenceInitializationRun.elapsed p b.completed ∧
      test.sample = ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2
        test.time).2 (0, i) ∧
      PublicDiscreteDraws.slotDraw (x.row.2 test.time).1 = PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 test.time).1 = i ∧
      ∃ q, ∃ h : (ReferenceInitializationRun.run x q).completed < n_boot p,
        (ReferenceInitializationRun.run x q).crossing = none ∧
        (ReferenceInitializationRun.run x q).activation f = some a ∧
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.run x q).completed ≤ test.time.val ∧
        test.time.val < ReferenceInitializationRun.elapsed p
          ((ReferenceInitializationRun.run x q).completed + 1) ∧
        ∃ u : Fin (ReferenceInitializationRun.elapsed p b.completed),
          u.val = test.time.val ∧
          b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f) u =
            ReferenceInitializationRun.ownEntry
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              (PublicDiscreteDraws.followerPlayer p.two_le_m f) test.time ∧
          0 < (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f) u).2.val.val ∧
          ReferenceInitializationRun.coordinatorLearner (ReferenceInitializationRun.run x q) = none ∧
          BootstrapPhysicalBlock.actions
            (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
            (BootstrapPhysicalBlock.run
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              test.time.val) test.time (coordinator p.two_le_m) =
            (BootstrapPhysicalBlock.tuple
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              test.time).val (coordinator p.two_le_m) ∧
          BootstrapPhysicalBlock.actions
            (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
            (BootstrapPhysicalBlock.run
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              test.time.val) test.time (PublicDiscreteDraws.followerPlayer p.two_le_m f) =
            (BootstrapPhysicalBlock.tuple
              (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h)
              test.time).val (PublicDiscreteDraws.followerPlayer p.two_le_m f) ∧ test.sent = none := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  obtain ⟨_, a, ha, u, hselected, hpositive, heq⟩ :=
    (mem_boundaryPrelaunchDownTests_iff x b i test).mp hmem
  have hselection := of_decide_eq_true hselected
  change a.val ≤ u.val + 1 ∧
    PublicDiscreteDraws.slotDraw (x.row.2
      (ReferencePrelaunchFollower.calendar
        (ReferenceInitializationRun.elapsed_le_T p b.completed) u)).1 =
        PublicDiscreteDraws.downSlot ∧ _ at hselection
  subst test
  obtain ⟨q, h, hnone, hactivation, hstart, hend, v, hv, hown⟩ :=
    run_active_history_origin x (n_boot p) (ActualReferenceInitializationBlock.refFollower i)
      a ha (ReferencePrelaunchFollower.calendar
        (ReferenceInitializationRun.elapsed_le_T p b.completed) u) u.isLt hselection.1
  have hvu : v = u := Fin.ext hv
  subst v
  refine ⟨a, ha, hselection.1, u.isLt, rfl, hselection.2.1, hselection.2.2,
    q, h, hnone, hactivation,
    hstart, hend, u, rfl, hown, hpositive, ?_, ?_, ?_, rfl⟩
  · change ReferenceInitializationRun.coordinatorLearner (ReferenceInitializationRun.run x q) = none
    simp only [ReferenceInitializationRun.coordinatorLearner, hnone, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte]
  · rw [BootstrapPhysicalBlock.actions_coordinator]
    apply BootstrapPhysicalBlock.coordinatorAction_down
    exact hselection.2.1
  · rw [BootstrapPhysicalBlock.actions_follower]
    have hnot : ActualReferenceInitializationBlock.refFollower i ∉
        (ReferenceInitializationRun.physical x (ReferenceInitializationRun.run x q) h).uninformed := by
      change ActualReferenceInitializationBlock.refFollower i ∉
        ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x q)
      rw [ReferenceInitializationRun.mem_uninformed, hactivation]
      intro he
      cases he
    rw [BootstrapPhysicalBlock.followerAction, dite_eq_right hnot]
    apply BootstrapPhysicalBlock.unoccupiedAction_down
    exact hselection.2.1

/-- Strict time order rules out repeated selected positives, even when the
affine samples themselves coincide. -/
theorem source_prelaunch_down_tests_pairwise
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) :
    (sourcePrelaunchDownTests rate rewards C_star C_h z i).Pairwise
      (fun a b => a.time.val < b.time.val) := by
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  have hw := (boundary_census x b i).1
  have hp : (AffineBatchDecoder.collected
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).downBatch).Pairwise
        (fun a b => a.time.val < b.time.val) := by
    unfold ReferenceInitializationRun.ordinary
    split_ifs
    · exact List.Pairwise.nil
    · split
      · exact List.Pairwise.nil
      · exact ReferencePrelaunchFollower.replay_collected_pairwise _ _ _ _ _ _
  rw [← hw] at hp
  have hpair : (boundaryPrelaunchDownTests x b i).Pairwise
      (fun a b => (testEntry a).time.val < (testEntry b).time.val) :=
    (List.pairwise_map (f := testEntry)
      (R := fun (a b : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) =>
        a.time.val < b.time.val)).mp hp
  exact hpair

/-- Membership and strict chronology give exactly one occurrence of every
retained selected positive, without any distinctness assumption on samples. -/
theorem source_prelaunch_down_tests_once
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) :
    ∀ test ∈ sourcePrelaunchDownTests rate rewards C_star C_h z i,
      (sourcePrelaunchDownTests rate rewards C_star C_h z i).count test = 1 := by
  have hd : (sourcePrelaunchDownTests rate rewards C_star C_h z i).Nodup :=
    (source_prelaunch_down_tests_pairwise rate rewards C_star C_h z i).imp
      (fun {a b} hab heq => by
        rw [heq] at hab
        exact (Nat.lt_irrefl _) hab)
  exact fun _ hmem => hd.count_of_mem hmem

private theorem run_completed_origin {n : ℕ} {eta : ReferencePrelaunchFollower.LearningRate}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (a : ReferencePrelaunchFollower.Activation p)
    (history : ReferencePrelaunchFollower.LocalHistory p n) (hn : n ≤ p.T) (us : List (Fin n))
    (state : ReferencePrelaunchFollower.State p eta) (hu : state.status = .unoccupied)
    (hk : state.downBatch.pending.length < AffineBatchDecoder.quota p)
    (hc : ∀ batch ∈ state.downBatch.completed, batch.length = AffineBatchDecoder.quota p)
    (batch : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (hb : batch ∈ (ReferencePrelaunchFollower.run i row a history hn us state).downBatch.completed) :
    batch ∈ state.downBatch.completed ∨
      ∃ pre u post, us = pre ++ u :: post ∧
        let before := ReferencePrelaunchFollower.run i row a history hn pre state
        AffineBatchDecoder.eligible (ReferencePrelaunchFollower.traceAt i row a
          (ReferencePrelaunchFollower.calendar hn u) (history u)
          (ReferencePrelaunchFollower.calendar hn u)) ∧
        before.downBatch.pending.length + 1 = AffineBatchDecoder.quota p ∧
        batch = before.downBatch.pending ++
          [AffineBatchDecoder.entry p (ReferencePrelaunchFollower.traceAt i row a
            (ReferencePrelaunchFollower.calendar hn u) (history u))
            (ReferencePrelaunchFollower.calendar hn u)] := by
  induction us generalizing state with
  | nil => exact Or.inl hb
  | cons u us ih =>
    have hspec := ReferencePrelaunchFollower.step_batch_spec i row a
      (ReferencePrelaunchFollower.calendar hn u) (history u) state hu hk hc
    have hu' := (ReferencePrelaunchFollower.step_registers i row a
      (ReferencePrelaunchFollower.calendar hn u) (history u) state).2.2.2.2.trans hu
    rcases ih (ReferencePrelaunchFollower.step i row a (ReferencePrelaunchFollower.calendar hn u) (history u) state)
        hu' hspec.1 hspec.2.1 hb with hold | hnew
    · have hmem : batch ∈ (AffineBatchDecoder.step p (ReferencePrelaunchFollower.traceAt i row a
          (ReferencePrelaunchFollower.calendar hn u) (history u))
          state.downBatch (ReferencePrelaunchFollower.calendar hn u)).completed := by
        simpa only [ReferencePrelaunchFollower.step, hu, ↓reduceIte,
          ReferencePrelaunchFollower.decodeAt_fst i row a (ReferencePrelaunchFollower.calendar hn u)
            (history u) state.downBatch hk] using hold
      unfold AffineBatchDecoder.step at hmem
      dsimp only at hmem
      split_ifs at hmem with hsmall
      · exact Or.inl hmem
      · have he : AffineBatchDecoder.eligible (ReferencePrelaunchFollower.traceAt i row a
            (ReferencePrelaunchFollower.calendar hn u) (history u)
            (ReferencePrelaunchFollower.calendar hn u)) := by
          by_contra hne
          simp only [AffineBatchDecoder.positiveAt, hne, ↓reduceIte, List.append_nil] at hsmall
          exact hsmall hk
        have hq : state.downBatch.pending.length + 1 = AffineBatchDecoder.quota p := by
          simp only [AffineBatchDecoder.positiveAt, he, ↓reduceIte, List.length_append,
            List.length_singleton] at hsmall
          omega
        simp only [List.mem_append, List.mem_singleton, AffineBatchDecoder.positiveAt, he,
          ↓reduceIte] at hmem
        rcases hmem with hold | heq
        · exact Or.inl hold
        · exact Or.inr ⟨[], u, us, rfl, he, hq, heq⟩
    · obtain ⟨pre, v, post, hindices, he, hq, heq⟩ := hnew
      refine Or.inr ⟨u :: pre, v, post, ?_, he, hq, heq⟩
      rw [List.cons_append, hindices]

/-- Every completed cohort comes from an actual quota-reaching call in the
canonical replay, with the raw solver output retained even when it is `none`.
The witness includes the full state before that call and its exact offset list. -/
theorem source_prelaunch_down_completed_transition
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (k : ℕ) (hk : k < (ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      (ReferenceInitializationRun.output (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate))
      (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let bank := (ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i)).downBatch
    ∃ a, b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = false ∧
      b.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
      ∃ pre u post,
        List.ofFn (fun v : Fin (ReferenceInitializationRun.elapsed p b.completed) => v) = pre ++ u :: post ∧
        let history := b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i))
        let hn := ReferenceInitializationRun.elapsed_le_T p b.completed
        let before := ReferencePrelaunchFollower.run i x.row a history hn pre (ReferencePrelaunchFollower.initial p rate.eta)
        let t := ReferencePrelaunchFollower.calendar hn u
        before.status = .unoccupied ∧
        AffineBatchDecoder.eligible (ReferencePrelaunchFollower.traceAt i x.row a t (history u) t) ∧
        before.downBatch.pending.length + 1 = AffineBatchDecoder.quota p ∧
        bank.completed[k] = before.downBatch.pending ++
          [AffineBatchDecoder.entry p (ReferencePrelaunchFollower.traceAt i x.row a t (history u)) t] ∧
        ReferencePrelaunchFollower.decodeAt i x.row a t (history u) before.downBatch =
          (⟨[], before.downBatch.completed ++ [bank.completed[k]]⟩,
            AffineBatchDecoder.batchOutput bank.completed[k]) ∧
        (ReferencePrelaunchFollower.step i x.row a t (history u) before).buffer =
          before.buffer ++ ReferencePrelaunchFollower.logAt i x.row a t (history u) ∧
        (ReferencePrelaunchFollower.step i x.row a t (history u) before).initializationFailure =
          (before.initializationFailure ||
            decide (ReferencePrelaunchFollower.passing_at rate.eta i x.row a t (history u) before.downBatch)) := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let f := ActualReferenceInitializationBlock.refFollower i
  have hb := List.getElem_mem hk
  change _ ∈ (ReferenceInitializationRun.ordinary x b f).downBatch.completed at hb
  cases hf : b.forcedFailure f
  · cases ha : b.activation f with
    | none =>
      simp only [ReferenceInitializationRun.ordinary, hf, Bool.false_eq_true, ↓reduceIte, ha,
        ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial, List.not_mem_nil] at hb
    | some a =>
      have hstate : ReferenceInitializationRun.ordinary x b f = ReferencePrelaunchFollower.replay rate.eta i x.row a
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f))
          (ReferenceInitializationRun.elapsed_le_T p b.completed) := by
        simp only [ReferenceInitializationRun.ordinary, hf, Bool.false_eq_true, ↓reduceIte, ha,
          ReferencePrelaunchFollower.atLaunch]
        rfl
      have hbatch : (ReferenceInitializationRun.ordinary x b f).downBatch.completed[k] ∈
          (ReferencePrelaunchFollower.replay rate.eta i x.row a
            (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f))
            (ReferenceInitializationRun.elapsed_le_T p b.completed)).downBatch.completed := by
        rw [← hstate]
        exact hb
      rcases run_completed_origin i x.row a
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f))
          (ReferenceInitializationRun.elapsed_le_T p b.completed) (List.ofFn (fun u => u))
          (ReferencePrelaunchFollower.initial p rate.eta) rfl (AffineBatchDecoder.quota_pos p)
          (by simp only [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial,
            List.not_mem_nil, false_implies, implies_true])
          _ hbatch with hempty | horigin
      · cases hempty
      · obtain ⟨pre, u, post, hindices, he, hq, heq⟩ := horigin
        have hu := (ReferencePrelaunchFollower.run_registers i x.row a
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f))
          (ReferenceInitializationRun.elapsed_le_T p b.completed) pre (ReferencePrelaunchFollower.initial p rate.eta)).2.2.2.2
        change _ = FollowerStatus.unoccupied at hu
        dsimp only [x, b, f] at hu
        refine ⟨a, rfl, rfl, pre, u, post, hindices, hu, he, hq, heq, ?_, ?_, ?_⟩
        · rw [heq]
          exact ReferencePrelaunchFollower.decodeAt_complete _ _ _ _ _ _ he hq
        · simp only [ReferencePrelaunchFollower.step, hu, ↓reduceIte]
        · simp only [ReferencePrelaunchFollower.step, hu, ↓reduceIte]
  · simp only [ReferenceInitializationRun.ordinary, hf, ↓reduceIte, ReferencePrelaunchFollower.forcedAtLaunch,
      ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial, List.not_mem_nil] at hb

/-- Boundary of cohort `k`, with `k = completed.length` denoting the pending
cohort even if it is empty. The initial boundary is activation minus one;
later boundaries are the previous cohort's actual last test plus one.
The result is optional and may equal T, where there is no next action. -/
def sourcePrelaunchDownCohortBoundary (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (k : ℕ) : Option ℕ :=
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let f := ActualReferenceInitializationBlock.refFollower i
  let bank := (ReferenceInitializationRun.ordinary x b f).downBatch
  if k = 0 then (b.activation f).map (fun a => a.val - 1)
  else (bank.completed[k - 1]?.bind List.getLast?).map (fun e => e.time.val + 1)

/-- Initial cohort creation, independent of its first positive test. The
activation may be the terminal T+1 value. -/
theorem source_prelaunch_down_initial_boundary (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let f := ActualReferenceInitializationBlock.refFollower i
    sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i 0 =
      (b.activation f).map (fun a => a.val - 1) ∧
    ∀ (a) (ha : b.activation f = some a),
      a.val - 1 ≤ ReferenceInitializationRun.elapsed p b.completed ∧
      ReferencePrelaunchFollower.replay rate.eta i x.row a
        (ReferencePrelaunchLifecycleReplay.prefixHistory
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m f))
          (a.val - 1) (by have := b.activation_le f a ha; omega))
        (by have := b.activation_le f a ha; have := ReferenceInitializationRun.elapsed_le_T p b.completed; omega) =
          ReferencePrelaunchFollower.initial p rate.eta := by
  dsimp only
  refine ⟨rfl, ?_⟩
  intro a ha
  have hle := (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).activation_le
    (ActualReferenceInitializationBlock.refFollower i) a ha
  refine ⟨by omega, ?_⟩
  apply ReferencePrelaunchFollower.replay_before_activation
  have := a.property.1
  omega

/-- Each actual completion creates the next cohort at its real reset. This
includes the final pending cohort, whether empty or nonempty, and permits a
reset boundary T without constructing an action at T. -/
theorem source_prelaunch_down_reset_boundary (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (k : ℕ) (hk : k < (ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      (ReferenceInitializationRun.output (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate))
      (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let bank := (ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i)).downBatch
    ∃ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p b.completed ∧
      bank.completed[k].getLast? = some ⟨t, (x.row.2 t).2 (0, i)⟩ ∧
      sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i (k + 1) =
        some (t.val + 1) := by
  dsimp only
  obtain ⟨a, _, _, pre, u, post, _, _, _, _, heq, _, _, _⟩ :=
    source_prelaunch_down_completed_transition rate rewards C_star C_h z i k hk
  have hlast := congrArg List.getLast? heq
  rw [List.getLast?_concat] at hlast
  refine ⟨ReferencePrelaunchFollower.calendar (ReferenceInitializationRun.elapsed_le_T p _) u, u.isLt, hlast, ?_⟩
  dsimp only [sourcePrelaunchDownCohortBoundary]
  rw [ite_eq_right (by omega : k + 1 ≠ 0), Nat.add_sub_cancel,
    List.getElem?_eq_getElem hk, Option.bind_some, hlast, Option.map_some]
  rfl

/-- Newly activated followers have no earlier selected positives. Forced
followers have their true initial state, with the forced failure bit retained.
Both are consequences of the literal generated ordinary projection. -/
theorem source_prelaunch_down_initial_cases (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let f := ActualReferenceInitializationBlock.refFollower i
    (b.forcedFailure f = true →
      ReferenceInitializationRun.ordinary x b f = ReferencePrelaunchFollower.initial p rate.eta ∧
      sourcePrelaunchDownTests rate rewards C_star C_h z i = [] ∧
      ReferenceInitializationRun.initializationFailure x b f = true) ∧
    (∀ a, b.activation f = some a → a.val = ReferenceInitializationRun.elapsed p b.completed + 1 →
      ReferenceInitializationRun.ordinary x b f = ReferencePrelaunchFollower.initial p rate.eta ∧
      sourcePrelaunchDownTests rate rewards C_star C_h z i = []) := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let f := ActualReferenceInitializationBlock.refFollower i
  constructor
  · intro hf
    change b.forcedFailure f = true at hf
    change ReferenceInitializationRun.ordinary x b f = _ ∧
      boundaryPrelaunchDownTests x b i = [] ∧
      ReferenceInitializationRun.initializationFailure x b f = true
    refine ⟨?_, ?_, ?_⟩
    · simp only [ReferenceInitializationRun.ordinary, hf, ↓reduceIte]
      rfl
    · dsimp only [boundaryPrelaunchDownTests]
      rw [show b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = true from hf]
      rfl
    · change (b.forcedFailure f || _) = true
      rw [hf, Bool.true_or]
  · intro a ha he
    change b.activation f = some a at ha
    change a.val = ReferenceInitializationRun.elapsed p b.completed + 1 at he
    have hstate : ReferenceInitializationRun.ordinary x b f = ReferencePrelaunchFollower.initial p rate.eta := by
      unfold ReferenceInitializationRun.ordinary
      split_ifs
      · rfl
      · rw [ha]
        apply ReferencePrelaunchFollower.replay_before_activation
        omega
    refine ⟨hstate, ?_⟩
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro test hmem
    obtain ⟨_, a', ha', u, hs, _, _⟩ :=
      (mem_boundaryPrelaunchDownTests_iff x b i test).mp hmem
    have haa : a' = a := Option.some.inj (ha'.symm.trans ha)
    have hactive := (of_decide_eq_true hs).1
    change a'.val ≤ u.val + 1 at hactive
    have := u.isLt
    rw [haa, he] at hactive
    omega

/-- Forced cohort creation is at the computed launch boundary. A forcing bit
cannot occur in a noncrossing generated output; that fact is produced here. -/
theorem source_prelaunch_down_forced_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1)) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let f := ActualReferenceInitializationBlock.refFollower i
    b.forcedFailure f = true → b.crossing.isSome = true ∧
      ∃ a, b.activation f = some a ∧ a.val = ReferenceInitializationRun.elapsed p b.completed + 1 ∧
        sourcePrelaunchDownCohortBoundary rate rewards C_star C_h z i 0 =
          some (ReferenceInitializationRun.elapsed p b.completed) := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let f := ActualReferenceInitializationBlock.refFollower i
  intro hf
  have hc : b.crossing.isSome = true := by
    cases he : b.crossing with
    | none =>
      have hfalse := ReferenceInitializationRun.run_no_forced_before_launch x (n_boot p) he f
      change b.forcedFailure f = false at hfalse
      rw [hfalse] at hf
      cases hf
    | some crossing => rfl
  obtain ⟨_, _, a, ha, he⟩ :=
    ReferenceCorrectedInitializationLaunch.output_forced_failure_retained
      rate z rewards C_star C_h hc i hf
  refine ⟨hc, a, ha, he, ?_⟩
  have hb := (source_prelaunch_down_initial_boundary rate rewards C_star C_h z i).1
  rw [hb, ha, Option.map_some, he, Nat.add_sub_cancel]

/-- Exhaustion without crossing has a terminal census and no launch payload.
It is distinct from a crossing whose elapsed time happens to equal T. -/
theorem source_prelaunch_down_no_crossing (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    (ReferenceInitializationRun.output x).crossing = none →
      ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed = p.T ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none := by
  dsimp only
  intro hc
  refine ⟨?_, (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff rate z rewards C_star C_h).2 hc⟩
  have hprogress := ReferenceInitializationRun.run_progress
    (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
    (n_boot p) le_rfl
  rcases hprogress with hcross | heq
  · change (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true at hcross
    rw [hc] at hcross
    cases hcross
  · change ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
      (n_boot p)).completed = p.T
    rw [heq]
    exact ReferenceInitializationRun.elapsed_all_blocks p

/-- The source launch stratum and the SAME full follower state in the generated
seed. In particular the carried bank is the census bank, without a supplied
seed equality. Forced and suppressed failure flags are retained separately. -/
theorem source_launch_down_cohort_provenance (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (i : Fin (p.m - 1))
    (hs : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed < p.T)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let s := ReferenceInitializationRun.elapsed p b.completed
    ∃ launchSource : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs,
      launchSource.val = z ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
        some (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h s hs launchSource) ∧
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h s hs launchSource).followers i =
        .ordinary (ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i))
          (ActiveFollowerLifecycle.initialMemory p) ∧
      ReferenceFollowerDecoderChronology.downBatchSeed
        (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h s hs launchSource) s ∧
      ReferenceInitializationRun.initializationFailure x b (ActualReferenceInitializationBlock.refFollower i) =
        (b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) ||
          (ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i)).initializationFailure) ∧
      ∃ a, b.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
        ((b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = true ∧
          ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i) =
            ReferencePrelaunchFollower.initial p rate.eta ∧ a.val = s + 1) ∨
         (b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = false ∧
          ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i) =
            ReferencePrelaunchFollower.replay rate.eta i x.row a
              (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ActualReferenceInitializationBlock.refFollower i)))
              (ReferenceInitializationRun.elapsed_le_T p b.completed))) := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let s := ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed
  let launchSource : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs := ⟨z, hc, rfl⟩
  have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec rate rewards C_star C_h s hs launchSource
  obtain ⟨active, hfields, _⟩ := ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
    rate z rewards C_star C_h hc
  have heq := Option.some.inj (hfields.1.symm.trans hseed.1)
  refine ⟨launchSource, rfl, hseed.1, ?_, hseed.2.2, rfl, ?_⟩
  · rw [← heq]
    exact hfields.2.2.2.2 i
  · obtain ⟨a, ha, hmemory⟩ := ReferenceCorrectedInitializationLaunch.output_memory_provenance
      z rewards C_star C_h rate hc i
    refine ⟨a, ha, ?_⟩
    rcases hmemory with hforced | hordinary
    · exact Or.inl ⟨hforced.1, hforced.2.1, hforced.2.2.1⟩
    · exact Or.inr ⟨hordinary.1, hordinary.2.1⟩

/-- A crossing at elapsed T still has its corrected launch payload, its next
round is T+1, and its physical suffix is empty. No Fin T value is made at T. -/
theorem source_prelaunch_down_terminal_crossing
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
    (ReferenceInitializationRun.output x).crossing.isSome = true →
      ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed = p.T →
      ∃ active, ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active p.T,
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active ∧
        ReferenceInitializationRun.launchRound x = p.T + 1 ∧
        (ReferenceActivePhysicalHorizon.run active z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards p.T 0
          (Nat.le_refl _) hmode).finalState = active ∧
        (ReferenceActivePhysicalHorizon.run active z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards p.T 0
          (Nat.le_refl _) hmode).records = [] := by
  dsimp only
  intro hc ht
  obtain ⟨active, hmode, hlaunch, hfinal, hrecords⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_terminal_run_zero rate z rewards C_star C_h hc ht
  exact ⟨active, hmode, hlaunch,
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_terminal_crossing rate z rewards C_star C_h hc ht).2,
    hfinal, hrecords⟩

end Bandits.Support.ReferenceGeneratedPrelaunchDownCohort

end
