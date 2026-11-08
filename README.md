# SquareRootBandits

A Lean 4 formalization of the main regret bound in
[Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness](https://arxiv.org/abs/2610.05688v2).

The paper establishes expected regret

$$
O\!\left(m^{3/2}\sqrt{KT}\log^2(KmT)\right)
$$

without collision information, shared randomness or a separate communication channel.

## Scope

This repository formalizes the main regret bound. The paper's polynomial-time computational complexity claim is not formalized.

The development includes the constructions and supporting results needed for the regret theorem: local policies, initialization, communication, coupling, error coverage and regret accounting. The main result provides a public-table guarantee uniform over reward matrices, with regret averaged over the players' private randomness.

See [CORRESPONDENCE.md](CORRESPONDENCE.md) for the exact statement, definitions and scope.

## Main theorem

The main declaration is

```lean
Bandits.Support.Frozen.MainRegret.exists_uniform_actual_main_regret_bound
```

Its statement and proof are in [MainRegret.lean](Bandits/Support/Frozen/MainRegret.lean). It bounds expected regret by an absolute constant times the named scale `BootstrapStartupCostScale.Q_boot`. The [scale definition and its power-form identity](Bandits/Support/BootstrapStartupCostScale.lean) give

$$
Q_{\mathrm{boot}}=m\sqrt m\sqrt{KT}\,b_N^2
  =m^{3/2}\sqrt{KT}\,b_N^2,
\qquad b_N=\lceil\log_2(N+1)\rceil,\quad N=2Km(T+1).
$$

## Building

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```bash
lake exe cache get
lake build
```

The toolchain is pinned to Lean **4.35.0**. The committed `lake-manifest.json` pins Mathlib and its dependencies. The first command downloads precompiled Mathlib artifacts; the project itself can take several hours to build from scratch.

To use the library:

```lean
import Bandits

#check Bandits.Support.Frozen.MainRegret.exists_uniform_actual_main_regret_bound
```

## Verification

The production library contains no `sorry` or custom axiom declarations. The main theorem depends only on the standard foundational axioms `propext`, `Classical.choice` and `Quot.sound`.

After building, run the kernel replay and transitive axiom audit:

```bash
lake env lean --run Audit/KernelReplay.lean \
  Bandits.Support.Frozen.MainRegret \
  Bandits.Support.Frozen.MainRegret.exists_uniform_actual_main_regret_bound
```

The audit requires all compiled module parts, inspects actual proof dependencies and replays the main module through Lean's kernel. Its implementation uses Lean's inspection APIs; it is separate from the mathematical library. Axiom checking establishes logical dependencies, while correspondence with the manuscript is documented separately.

## Repository layout

| Location | Contents |
| --- | --- |
| [Bandits.lean](Bandits.lean) | Library entry point |
| [Bandits/Support/](Bandits/Support/) | Required definitions and supporting proofs |
| [MainRegret.lean](Bandits/Support/Frozen/MainRegret.lean) | Main regret theorem |
| [Audit/KernelReplay.lean](Audit/KernelReplay.lean) | Kernel replay and axiom audit |
| [CORRESPONDENCE.md](CORRESPONDENCE.md) | Paper-to-Lean statement map and scope |
| [formalization.yaml](formalization.yaml) | Formalization provenance |
| [CITATION.cff](CITATION.cff) | Citation information |

## Development and license

The formalization was developed with Codex coding agents under maintainer supervision. Lean checks the formal proofs. Provenance and review scope are recorded in [formalization.yaml](formalization.yaml).

Released under the [Apache-2.0 license](LICENSE). Existing source attribution is retained.
