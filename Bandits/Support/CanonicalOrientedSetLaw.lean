/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ProductSetDistribution
public import Bandits.Support.FiniteOrientationDisintegration
import Mathlib.Tactic.Order

/-!
# Canonical product-set law with a globally normalized slow set

This module specializes the accepted product-set and finite-orientation laws
to the actual arm carrier `Fin K`. Its source formulas are in
`sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`. The slow carrier is
the existing supported `(m - 1)`-set subtype. We prove its global mass by
reindexing the supported `(U,j)` pairs against supported `(S,j)` pairs using
`U = S.erase j` and `S = insert j U`.

These are internal finite-law results. The module does not implement a sampler,
a fresh-stream realization, or an adaptive conditional process.
-/

public section

open scoped BigOperators

namespace Bandits.Support.CanonicalOrientedSetLaw

open Bandits.Support.ProductSetLaw
open Bandits.Support.FiniteOrientationDisintegration

/-- The existing product-law support subtype at cardinality `m - 1`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-23`. -/
abbrev SlowSet (K m : ℕ) := ProductSetLaw.ProductSet K (m - 1)

/-- The generic partition function on `Fin K` is the accepted canonical
product-law normalizer.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:10-13`. -/
theorem partitionFunction_univ_eq_normalizer {K m : ℕ} (w : Fin K → ℝ) :
    FiniteOrientationDisintegration.partitionFunction (Finset.univ : Finset (Fin K)) m w =
      ProductSetLaw.normalizer m w := rfl

/-- The slow carrier's cardinality is `m - 1`, so one insertion gives an `m`-set.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-23`. -/
theorem slowSet_card {K m : ℕ} (hm : 2 ≤ m) (U : SlowSet K m) :
    U.1.card + 1 = m := by
  have hcard := (Finset.mem_powersetCard.mp U.2).2
  omega

/-- Every supported slow set has a nonempty complement under `m < K`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-23`. -/
theorem slowSet_complement_nonempty {K m : ℕ} (hm : 2 ≤ m) (hmK : m < K)
    (U : SlowSet K m) : ((Finset.univ : Finset (Fin K)) \ U.1).Nonempty := by
  have hcard := (Finset.mem_powersetCard.mp U.2).2
  have hlt : U.1.card < K := by omega
  have huniv : (Finset.univ : Finset (Fin K)).card = K := by simp
  exact Finset.sdiff_nonempty_of_card_lt_card (by simpa [huniv] using hlt)

/-- The manuscript slow-set marginal specialized to the supported `(m - 1)`-sets
of the actual `Fin K` arm carrier. All validity data is derived from the
subtype and the stated source premises.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-23`. -/
@[expose] noncomputable def slowMarginal {K m : ℕ} (w anchor : Fin K → ℝ)
    (hm : 2 ≤ m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : SlowSet K m) : ℝ :=
  FiniteOrientationDisintegration.slowMarginal (Finset.univ : Finset (Fin K)) m
    w anchor U.1 (Finset.subset_univ _) (slowSet_card hm U)
    (slowSet_complement_nonempty hm hmK U)
    (fun i _ => hw i) (fun i _ => hanchor i)

/-- Every supported slow set has positive marginal mass. -/
theorem slowMarginal_pos {K m : ℕ} (w anchor : Fin K → ℝ)
    (hm : 2 ≤ m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : SlowSet K m) :
    0 < slowMarginal w anchor hm hmK hw hanchor U := by
  exact FiniteOrientationDisintegration.slowMarginal_pos
    (Finset.univ : Finset (Fin K)) U.1 m w anchor (Finset.subset_univ _)
    (slowSet_card hm U) (slowSet_complement_nonempty hm hmK U)
    (fun i _ => hw i) (fun i _ => hanchor i)

/-- On the inserted supported set, the accepted oriented joint mass is exactly
canonical `Q` times the accepted orientation probability.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:11,16-19,30-35`. -/
theorem orientedJointMass_eq_Q_mul_orientationProbability {K m : ℕ}
    (w anchor : Fin K → ℝ) (_hm : 2 ≤ m) (_hmK : m < K)
    (hw : ∀ i, 0 < w i) (hanchor : ∀ i, 0 < anchor i)
    (U : SlowSet K m)
    (j : {j // j ∈ (Finset.univ : Finset (Fin K)) \ U.1}) :
    FiniteOrientationDisintegration.orientedJointMass (Finset.univ : Finset (Fin K))
      m w anchor U.1 (Finset.subset_univ _) (slowSet_card _hm U)
        (fun i _ => hw i) (fun i _ => hanchor i) j =
      ProductSetLaw.Q m w
        ⟨insert j.1 U.1, by
          rcases Finset.mem_sdiff.mp j.2 with ⟨hj, hjU⟩
          exact Finset.mem_powersetCard.mpr
            ⟨Finset.insert_subset hj (Finset.subset_univ _),
              (Finset.card_insert_of_notMem hjU).trans (slowSet_card _hm U)⟩⟩ *
        FiniteOrientationDisintegration.orientationProbability anchor (insert j.1 U.1)
          (Finset.insert_nonempty _ _)
          (fun i _hi => hanchor i)
          ⟨j.1, Finset.mem_insert_self _ _⟩ := by
  have hnormalizer :
      FiniteOrientationDisintegration.partitionFunction
        (Finset.univ : Finset (Fin K)) m w = ProductSetLaw.normalizer m w :=
    partitionFunction_univ_eq_normalizer w
  rw [FiniteOrientationDisintegration.orientedJointMass, hnormalizer]
  change ((∏ i ∈ insert j.1 U.1, w i) / ProductSetLaw.normalizer m w) *
      FiniteOrientationDisintegration.orientationProbability anchor (insert j.1 U.1)
        _ _ _ =
    ((∏ i ∈ insert j.1 U.1, w i) / ProductSetLaw.normalizer m w) *
      FiniteOrientationDisintegration.orientationProbability anchor (insert j.1 U.1) _ _ _
  rfl

/-- Reindexing the supported insertion pairs preserves their total oriented
mass. This is the finite bijection `U = S.erase j`, `S = insert j U`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:20-23,30-37`. -/
private theorem insertion_pair_sum_eq_oriented_set_sum {K m : ℕ}
    (w anchor : Fin K → ℝ) (hm : 2 ≤ m) :
    (∑ U ∈ ProductSetLaw.support K (m - 1),
      ∑ j ∈ ((Finset.univ : Finset (Fin K)) \ U).attach,
        ((∏ i ∈ insert j.1 U, w i) /
          FiniteOrientationDisintegration.partitionFunction
            (Finset.univ : Finset (Fin K)) m w) *
          ((1 / anchor j.1) / ∑ i ∈ insert j.1 U, 1 / anchor i)) =
    (∑ S ∈ ProductSetLaw.support K m,
      ∑ j ∈ S.attach,
        ((∏ i ∈ S, w i) /
          FiniteOrientationDisintegration.partitionFunction
            (Finset.univ : Finset (Fin K)) m w) *
          ((1 / anchor j.1) / ∑ i ∈ S, 1 / anchor i)) := by
  classical
  let A := ProductSetLaw.support K (m - 1)
  let B := ProductSetLaw.support K m
  let domainFib : Finset (Fin K) → Finset (Fin K) :=
    fun U => (Finset.univ : Finset (Fin K)) \ U
  let raw (T : Finset (Fin K)) (j : Fin K) : ℝ :=
    ((∏ i ∈ T, w i) /
      FiniteOrientationDisintegration.partitionFunction
        (Finset.univ : Finset (Fin K)) m w) *
      ((1 / anchor j) / ∑ i ∈ T, 1 / anchor i)
  have hpair :
    (∑ U ∈ A, ∑ j ∈ (domainFib U).attach, raw (insert j.1 U) j.1) =
        ∑ S ∈ B, ∑ j ∈ S.attach, raw S j.1 := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    apply Finset.sum_bij (fun p _ => ⟨insert p.2.1 p.1, ⟨p.2.1, Finset.mem_insert_self _ _⟩⟩)
    · intro p hp
      obtain ⟨hU, hj⟩ := Finset.mem_sigma.mp hp
      have hjmem : p.2.1 ∈ domainFib p.1 := p.2.2
      rcases Finset.mem_sdiff.mp hjmem with ⟨hjU, hjnot⟩
      have hcard : p.1.card = m - 1 := by
        simpa [A, ProductSetLaw.support] using
          (Finset.mem_powersetCard.mp hU).2
      have hsize : p.1.card + 1 = m := by
        rw [hcard]
        exact Nat.sub_add_cancel (by omega)
      have hS : insert p.2.1 p.1 ∈ B := by
        apply Finset.mem_powersetCard.mpr
        exact ⟨Finset.insert_subset hjU (Finset.subset_univ _), by
          rw [Finset.card_insert_of_notMem hjnot]
          simpa [B, ProductSetLaw.support] using hsize⟩
      apply Finset.mem_sigma.mpr
      exact ⟨hS, Finset.mem_attach _ _⟩
    · intro p hp q hq hpq
      have hsets : insert p.2.1 p.1 = insert q.2.1 q.1 := congrArg Sigma.fst hpq
      have hj : p.2.1 = q.2.1 := congrArg (fun r => r.2.1) hpq
      have hpnot : p.2.1 ∉ p.1 := (Finset.mem_sdiff.mp p.2.2).2
      have hqnot : q.2.1 ∉ q.1 := (Finset.mem_sdiff.mp q.2.2).2
      have hsets' := congrArg (fun T : Finset (Fin K) => T.erase p.2.1) hsets
      rw [Finset.erase_insert hpnot, hj, Finset.erase_insert hqnot] at hsets'
      exact Sigma.subtype_ext hsets' hj
    · intro q hq
      obtain ⟨hS, hj⟩ := Finset.mem_sigma.mp hq
      have hjS : q.2.1 ∈ q.1 := q.2.2
      let U := q.1.erase q.2.1
      have hcardS := (Finset.mem_powersetCard.mp (show q.1 ∈ B from hS)).2
      have hU : U ∈ A := by
        apply Finset.mem_powersetCard.mpr
        refine ⟨(Finset.erase_subset _ _).trans
          (Finset.mem_powersetCard.mp (show q.1 ∈ B from hS)).1, ?_⟩
        dsimp [U]
        rw [Finset.card_erase_of_mem hjS]
        omega
      have hjU : q.2.1 ∈ domainFib U := by
        dsimp [domainFib, U]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.notMem_erase _ _⟩
      have hpre : (⟨U, (⟨q.2.1, hjU⟩ : {i // i ∈ domainFib U})⟩ :
          Sigma fun T : Finset (Fin K) => {i // i ∈ domainFib T}) ∈
          A.sigma (fun T => (domainFib T).attach) := by
        exact Finset.mem_sigma.mpr ⟨hU, Finset.mem_attach _ _⟩
      refine ⟨⟨U, (⟨q.2.1, hjU⟩ : {i // i ∈ domainFib U})⟩, hpre, ?_⟩
      have hsets : insert q.2.1 U = q.1 := by
        dsimp [U]
        exact Finset.insert_erase hjS
      exact Sigma.subtype_ext hsets rfl
    · intro p hp
      rfl
  exact hpair

/-- The global slow marginal sums to one. The proof sums the existing joint
mass over supported insertion pairs, reindexes by insert/erase, and applies the
accepted `Q` and orientation normalizations.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-23,30-37`. -/
theorem slowMarginal_sum_eq_one {K m : ℕ} (w anchor : Fin K → ℝ)
    (hm : 2 ≤ m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) :
    (∑ U : SlowSet K m, slowMarginal w anchor hm hmK hw hanchor U) = 1 := by
  classical
  let A := ProductSetLaw.support K (m - 1)
  let rawKernel (T : Finset (Fin K)) (j : Fin K) : ℝ :=
    ((∏ i ∈ T, w i) /
      FiniteOrientationDisintegration.partitionFunction
        (Finset.univ : Finset (Fin K)) m w) *
      ((1 / anchor j) / ∑ i ∈ T, 1 / anchor i)
  let rawSlow (U : Finset (Fin K)) : ℝ :=
    ∑ j ∈ ((Finset.univ : Finset (Fin K)) \ U).attach,
      rawKernel (insert j.1 U) j.1
  let rawSetMass (S : Finset (Fin K)) : ℝ :=
    (∏ i ∈ S, w i) /
      FiniteOrientationDisintegration.partitionFunction
        (Finset.univ : Finset (Fin K)) m w
  have hpoint (U : SlowSet K m) : slowMarginal w anchor hm hmK hw hanchor U = rawSlow U.1 := by
    unfold slowMarginal rawSlow rawKernel FiniteOrientationDisintegration.slowMarginal
    apply Finset.sum_congr rfl
    intro j hj
    rfl
  calc
    (∑ U : SlowSet K m, slowMarginal w anchor hm hmK hw hanchor U) =
        ∑ U : SlowSet K m, rawSlow U.1 := by
      apply Finset.sum_congr rfl
      intro U hU
      exact hpoint U
    _ = ∑ U ∈ A, rawSlow U := by
      symm
      exact Finset.sum_subtype A (by intro U; rfl) rawSlow
    _ = ∑ U ∈ A,
          ∑ j ∈ ((Finset.univ : Finset (Fin K)) \ U).attach,
            rawKernel (insert j.1 U) j.1 := by
      rfl
    _ = ∑ S ∈ ProductSetLaw.support K m,
          ∑ j ∈ S.attach,
            ((∏ i ∈ S, w i) /
              FiniteOrientationDisintegration.partitionFunction
                (Finset.univ : Finset (Fin K)) m w) *
              ((1 / anchor j.1) / ∑ i ∈ S, 1 / anchor i) := by
      exact insertion_pair_sum_eq_oriented_set_sum w anchor hm
    _ = ∑ S ∈ ProductSetLaw.support K m, rawSetMass S := by
      have hnormalizer :
          FiniteOrientationDisintegration.partitionFunction
            (Finset.univ : Finset (Fin K)) m w = ProductSetLaw.normalizer m w :=
        partitionFunction_univ_eq_normalizer w
      apply Finset.sum_congr rfl
      intro S hS
      have hSnonempty : S.Nonempty := by
        apply Finset.card_pos.mp
        rw [(Finset.mem_powersetCard.mp hS).2]
        omega
      have horient := FiniteOrientationDisintegration.orientationProbability_sum_eq_one
        anchor S hSnonempty (fun i hi => hanchor i)
      calc
        (∑ j ∈ S.attach,
            ((∏ i ∈ S, w i) /
              FiniteOrientationDisintegration.partitionFunction
                (Finset.univ : Finset (Fin K)) m w) *
              ((1 / anchor j.1) / ∑ i ∈ S, 1 / anchor i)) =
            ∑ j ∈ S.attach,
              rawSetMass S *
                FiniteOrientationDisintegration.orientationProbability anchor S
                  hSnonempty (fun i hi => hanchor i) j := by
          apply Finset.sum_congr rfl
          intro j hj
          rfl
        _ = rawSetMass S *
            (∑ j ∈ S.attach,
              FiniteOrientationDisintegration.orientationProbability anchor S
                hSnonempty (fun i hi => hanchor i) j) := by
          rw [← Finset.mul_sum]
        _ = rawSetMass S := by
          rw [horient]
          simp
    _ = ∑ S : ProductSetLaw.ProductSet K m, ProductSetLaw.Q m w S := by
      have hnormalizer :
          FiniteOrientationDisintegration.partitionFunction
            (Finset.univ : Finset (Fin K)) m w = ProductSetLaw.normalizer m w := rfl
      have hrawQ (S : ProductSetLaw.ProductSet K m) :
          rawSetMass S.1 = ProductSetLaw.Q m w S := by
        change (∏ i ∈ S.1, w i) /
          FiniteOrientationDisintegration.partitionFunction
            (Finset.univ : Finset (Fin K)) m w = ProductSetLaw.Q m w S
        rw [hnormalizer]
        rfl
      calc
        _ = ∑ S : ProductSetLaw.ProductSet K m, rawSetMass S.1 :=
          Finset.sum_subtype (ProductSetLaw.support K m) (by intro S; rfl) rawSetMass
        _ = ∑ S : ProductSetLaw.ProductSet K m, ProductSetLaw.Q m w S := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hrawQ S
    _ = 1 := ProductSetLaw.Q_sum_eq_one w (by omega) hmK hw

/-- The actual PMF of the globally normalized slow-set masses. -/
@[expose] noncomputable def slowSetPMF {K m : ℕ} (w anchor : Fin K → ℝ)
    (hm : 2 ≤ m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) : PMF (SlowSet K m) :=
  PMF.ofFintype (fun U => ENNReal.ofReal (slowMarginal w anchor hm hmK hw hanchor U)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)]
    · rw [slowMarginal_sum_eq_one w anchor hm hmK hw hanchor]
      simp
    · intro U hU
      exact (slowMarginal_pos w anchor hm hmK hw hanchor U).le)

/-- Pointwise ENNReal mass of the global slow-set PMF. -/
theorem slowSetPMF_apply {K m : ℕ} (w anchor : Fin K → ℝ)
    (hm : 2 ≤ m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : SlowSet K m) :
    slowSetPMF w anchor hm hmK hw hanchor U =
      ENNReal.ofReal (slowMarginal w anchor hm hmK hw hanchor U) := by
  simp [slowSetPMF]

/-- Reading a point mass of the global slow-set PMF as a real recovers the
source slow marginal. -/
theorem slowSetPMF_toReal_apply {K m : ℕ} (w anchor : Fin K → ℝ)
    (hm : 2 ≤ m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : SlowSet K m) :
    (slowSetPMF w anchor hm hmK hw hanchor U).toReal =
      slowMarginal w anchor hm hmK hw hanchor U := by
  rw [slowSetPMF_apply]
  exact ENNReal.toReal_ofReal (slowMarginal_pos w anchor hm hmK hw hanchor U).le

/-- Every supported slow-set PMF atom is positive. -/
theorem slowSetPMF_apply_pos {K m : ℕ} (w anchor : Fin K → ℝ)
    (hm : 2 ≤ m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (U : SlowSet K m) :
    0 < slowSetPMF w anchor hm hmK hw hanchor U := by
  rw [slowSetPMF_apply]
  exact ENNReal.ofReal_pos.mpr (slowMarginal_pos w anchor hm hmK hw hanchor U)

/-- The supported slow set obtained by erasing one designated fast arm. -/
@[expose] def eraseSlowSet {K m : ℕ} (_hm : 2 ≤ m)
    (S : ProductSetLaw.ProductSet K m) (j : {j // j ∈ S.1}) : SlowSet K m := by
  have hcard := (Finset.mem_powersetCard.mp S.2).2
  refine ⟨S.1.erase j.1, Finset.mem_powersetCard.mpr
    ⟨(Finset.erase_subset _ _).trans (Finset.mem_powersetCard.mp S.2).1, ?_⟩⟩
  rw [Finset.card_erase_of_mem j.2, hcard]

/-- The erased fast arm remains a genuine complement candidate. -/
@[expose] def erasedFastCandidate {K m : ℕ} (hm : 2 ≤ m)
    (S : ProductSetLaw.ProductSet K m) (j : {j // j ∈ S.1}) :
    {i // i ∈ (Finset.univ : Finset (Fin K)) \ (eraseSlowSet hm S j).1} :=
  ⟨j.1, Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _, Finset.notMem_erase _ _⟩⟩

/-- Reinsertion after erasure recovers the original supported set. -/
theorem insert_erasedSlowSet {K m : ℕ} (hm : 2 ≤ m)
    (S : ProductSetLaw.ProductSet K m) (j : {j // j ∈ S.1}) :
    insert (erasedFastCandidate hm S j).1 (eraseSlowSet hm S j).1 = S.1 := by
  exact Finset.insert_erase j.2

/-- The accepted conditional fast-arm law specialized to a supported slow set
on `Fin K`.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:24-29`. -/
@[expose] noncomputable def fastArmConditionalMass {K m : ℕ}
    (w anchor : Fin K → ℝ) (hm : 2 ≤ m) (hmK : m < K)
    (hw : ∀ i, 0 < w i) (hanchor : ∀ i, 0 < anchor i)
    (U : SlowSet K m) (j : {j // j ∈ (Finset.univ : Finset (Fin K)) \ U.1}) : ℝ :=
  FiniteOrientationDisintegration.conditionalFastLaw
    (Finset.univ : Finset (Fin K)) w anchor U.1 (Finset.subset_univ _)
    (slowSet_complement_nonempty hm hmK U)
    (fun i _ => hw i) (fun i _ => hanchor i) j

/-- For each supported `S`, summing the two-stage insertion masses over all
deletions of one arm recovers canonical `Q(S)`. The pointwise step uses the
accepted disintegration theorem; the final sum uses the accepted orientation
normalization.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-37`. -/
theorem twoStageInsertion_sum_eq_Q {K m : ℕ} (w anchor : Fin K → ℝ)
    (hm : 2 ≤ m) (hmK : m < K) (hw : ∀ i, 0 < w i)
    (hanchor : ∀ i, 0 < anchor i) (S : ProductSetLaw.ProductSet K m) :
    (∑ j : {j // j ∈ S.1},
      slowMarginal w anchor hm hmK hw hanchor (eraseSlowSet hm S j) *
        fastArmConditionalMass w anchor hm hmK hw hanchor
          (eraseSlowSet hm S j) (erasedFastCandidate hm S j)) =
      ProductSetLaw.Q m w S := by
  classical
  have hSnonempty : S.1.Nonempty := by
    apply Finset.card_pos.mp
    rw [(Finset.mem_powersetCard.mp S.2).2]
    omega
  have hSanchor : ∀ i ∈ S.1, 0 < anchor i := fun i _ => hanchor i
  have horient := FiniteOrientationDisintegration.orientationProbability_sum_eq_one
    anchor S.1 hSnonempty hSanchor
  have horientType :
      (∑ j : {j // j ∈ S.1},
        FiniteOrientationDisintegration.orientationProbability anchor S.1
          hSnonempty hSanchor j) = 1 := by
    simpa only [Finset.univ_eq_attach] using horient
  have hpoint (j : {j // j ∈ S.1}) :
      slowMarginal w anchor hm hmK hw hanchor (eraseSlowSet hm S j) *
          fastArmConditionalMass w anchor hm hmK hw hanchor
            (eraseSlowSet hm S j) (erasedFastCandidate hm S j) =
        ProductSetLaw.Q m w S *
          FiniteOrientationDisintegration.orientationProbability anchor S.1
            hSnonempty hSanchor j := by
    let U := eraseSlowSet hm S j
    let k := erasedFastCandidate hm S j
    have hU : U.1 ⊆ Finset.univ := Finset.subset_univ _
    have hsize : U.1.card + 1 = m := slowSet_card hm U
    have hcandidates : ((Finset.univ : Finset (Fin K)) \ U.1).Nonempty :=
      slowSet_complement_nonempty hm hmK U
    have hdis :=
      FiniteOrientationDisintegration.orientedJointMass_eq_slowMarginal_mul_conditionalFastLaw
        (Finset.univ : Finset (Fin K)) U.1 m w anchor hU hsize hcandidates
        (fun i _ => hw i) (fun i _ => hanchor i) k
    have hcanonical := orientedJointMass_eq_Q_mul_orientationProbability
      w anchor hm hmK hw hanchor U k
    have hinsert : insert k.1 U.1 = S.1 := insert_erasedSlowSet hm S j
    have hinsertSupport : insert k.1 U.1 ∈ ProductSetLaw.support K m := by
      rcases Finset.mem_sdiff.mp k.2 with ⟨hk, hkU⟩
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.insert_subset hk hU,
          (Finset.card_insert_of_notMem hkU).trans hsize⟩
    let S' : ProductSetLaw.ProductSet K m := ⟨insert k.1 U.1, hinsertSupport⟩
    have hS' : S' = S := Subtype.ext hinsert
    have hQ : ProductSetLaw.Q m w S' = ProductSetLaw.Q m w S :=
      congrArg (ProductSetLaw.Q m w) hS'
    have halpha :
        FiniteOrientationDisintegration.orientationProbability anchor (insert k.1 U.1)
            (Finset.insert_nonempty _ _) (fun i _ => hanchor i)
            ⟨k.1, Finset.mem_insert_self _ _⟩ =
          FiniteOrientationDisintegration.orientationProbability anchor S.1
            hSnonempty hSanchor j := by
      unfold FiniteOrientationDisintegration.orientationProbability
      have hk : k.1 = j.1 := rfl
      have hinsertJ : insert j.1 U.1 = S.1 := by
        simpa only [hk] using hinsert
      rw [hk, hinsertJ]
    calc
      _ = FiniteOrientationDisintegration.orientedJointMass
          (Finset.univ : Finset (Fin K)) m w anchor U.1 hU hsize
          (fun i _ => hw i) (fun i _ => hanchor i) k := by
        simpa [slowMarginal, fastArmConditionalMass] using hdis.symm
      _ = ProductSetLaw.Q m w S *
            FiniteOrientationDisintegration.orientationProbability anchor S.1
              hSnonempty hSanchor j := by
        change _ = ProductSetLaw.Q m w S' *
          FiniteOrientationDisintegration.orientationProbability anchor (insert k.1 U.1)
            (Finset.insert_nonempty _ _) (fun i _ => hanchor i)
            ⟨k.1, Finset.mem_insert_self _ _⟩ at hcanonical
        rw [hQ, halpha] at hcanonical
        exact hcanonical
  calc
    _ = ∑ j : {j // j ∈ S.1},
          ProductSetLaw.Q m w S *
            FiniteOrientationDisintegration.orientationProbability anchor S.1
              hSnonempty hSanchor j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hpoint j
    _ = ProductSetLaw.Q m w S := by
      rw [← Finset.mul_sum, horientType]
      simp

/-- The ENNReal mass of the two-stage insertion event agrees with the
canonical product-set PMF at every supported set.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:7-37`. -/
theorem twoStageInsertionPMF_sum_eq_productSetPMF {K m : ℕ}
    (w anchor : Fin K → ℝ) (hm : 2 ≤ m) (hmK : m < K)
    (hw : ∀ i, 0 < w i) (hanchor : ∀ i, 0 < anchor i)
    (S : ProductSetLaw.ProductSet K m) :
    (∑ j : {j // j ∈ S.1},
      slowSetPMF w anchor hm hmK hw hanchor (eraseSlowSet hm S j) *
        ENNReal.ofReal
          (fastArmConditionalMass w anchor hm hmK hw hanchor
            (eraseSlowSet hm S j) (erasedFastCandidate hm S j))) =
      ProductSetDistribution.productSetPMF w (by omega) hmK hw S := by
  classical
  have hcond (j : {j // j ∈ S.1}) :
      0 < fastArmConditionalMass w anchor hm hmK hw hanchor
        (eraseSlowSet hm S j) (erasedFastCandidate hm S j) := by
    exact FiniteOrientationDisintegration.conditionalFastLaw_pos
      (Finset.univ : Finset (Fin K)) (eraseSlowSet hm S j).1 w anchor
      (Finset.subset_univ _) (slowSet_complement_nonempty hm hmK (eraseSlowSet hm S j))
      (fun i _ => hw i) (fun i _ => hanchor i) (erasedFastCandidate hm S j)
  calc
    _ = ENNReal.ofReal
          (∑ j : {j // j ∈ S.1},
            slowMarginal w anchor hm hmK hw hanchor (eraseSlowSet hm S j) *
              fastArmConditionalMass w anchor hm hmK hw hanchor
                (eraseSlowSet hm S j) (erasedFastCandidate hm S j)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [slowSetPMF_apply]
        exact (ENNReal.ofReal_mul
          (slowMarginal_pos w anchor hm hmK hw hanchor (eraseSlowSet hm S j)).le).symm
      · intro j hj
        exact mul_nonneg
          (slowMarginal_pos w anchor hm hmK hw hanchor (eraseSlowSet hm S j)).le
          (hcond j).le
    _ = ENNReal.ofReal (ProductSetLaw.Q m w S) := by
      rw [twoStageInsertion_sum_eq_Q w anchor hm hmK hw hanchor S]
    _ = ProductSetDistribution.productSetPMF w (by omega) hmK hw S := by
      symm
      exact ProductSetDistribution.productSetPMF_apply_eq_Q w (by omega) hmK hw S

end Bandits.Support.CanonicalOrientedSetLaw

end
