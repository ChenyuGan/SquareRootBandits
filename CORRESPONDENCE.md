# Correspondence with the paper

Paper reference: [arXiv:2610.05688v2](https://arxiv.org/abs/2610.05688v2).

The scope is the regret component of the main result, together with the public-table probability guarantee and the local-policy constructions needed for it. The polynomial-time sampling and execution claim is not formalized.

## Main result

The public entry point is

```lean
Bandits.Support.Frozen.MainRegret.exists_uniform_actual_main_regret_bound
```

See [the complete Lean declaration](Bandits/Support/Frozen/MainRegret.lean). Its existential constants precede the parameter quantifier, so they are uniform in the problem dimensions. For every admissible parameter tuple it supplies measurable decisions, a measurable good-public-output event with complement probability at most `5 / N`, and the regret guarantee for every reward matrix on every good published output. The regret expectation is over private randomness, conditional on the published output.

The order is important: the reward matrix is universally quantified after the good published output is fixed. The public table may therefore be known when the reward matrix is chosen.

## Definitions and notation

| Paper object | Lean location |
| --- | --- |
| Integers `2 <= m < K`, `T >= 1`; `N = 2 K m (T+1)` and ceiling bit length `b_N` | [ConstructorDimensions](Bandits/Support/ConstructorDimensions.lean): `Parameters`, `N`, `b_N` |
| Regret scale `m^(3/2) sqrt(KT) b_N^2` | [BootstrapStartupCostScale](Bandits/Support/BootstrapStartupCostScale.lean): `Q_boot`, `Q_boot_eq_source_rpow` |
| Published output, its sampling law and the good-output event | [CompletePublicTable](Bandits/Support/CompletePublicTable.lean) |
| Reward matrices | [FiniteBanditModel](Bandits/Support/FiniteBanditModel.lean): `RewardMatrix` |
| Bounded local histories, rollout and private expected regret | [FiniteHorizonBoundedLocalRollout](Bandits/Support/FiniteHorizonBoundedLocalRollout.lean) |
| Product law of role-private randomness | [FiniteHorizonRolePrivateLaw](Bandits/Support/FiniteHorizonRolePrivateLaw.lean): `nu` |
| Actual local decisions and their final promotion to the main bound | [ActualMainRegretLocalPolicyPromotion](Bandits/Support/ActualMainRegretLocalPolicyPromotion.lean): `decision` and the main theorem provider |

`Q_boot` is written as `m * sqrt(m) * sqrt(K*T) * b_N^2`; the named power-form theorem proves its equality with `m^(3/2) * sqrt(K*T) * b_N^2`. The parameter domain, dimensions and scales are defined in Lean, rather than supplied as additional numerical assumptions.

## Reading the development

The supporting modules construct and relate the logical learner, reference execution, actual reward-only local protocol, initialization, communication and error events. Internal results are supporting mathematics; the main source-facing claim is the declaration linked above. This repository does not claim that every separately numbered statement of the article has an independently audited source-facing export.

Source comments retain the filenames, labels and line references of working LaTeX sources. These are historical source identifiers, not paths to manuscript files distributed in this repository. Historical development-admission references point to a private audit archive. The public paper is linked above; manuscript drafts and development logs are not bundled.

The mathematical modules are exported without proof refactoring. Seven historical VM paths were sanitized inside module comments; the surrounding declarations and proofs are unchanged. The publication entry file imports the main theorem and its complete public and proof-only dependency closure. Toolchain and dependency revisions are pinned in the build files.
