# Characterizing Language Generation in the Limit

Lean 4 code accompanying **Characterizing Language Generation in the Limit:
Finite Witnesses and a Separation-Width Hierarchy**, by **Xiaoyu Li, Andi Han,
Jiaojiao Jiang, and Junbin Gao**.

**Paper:** [arXiv:2609.10525](https://arxiv.org/abs/2609.10525)
| [HTML (v1)](https://arxiv.org/html/2609.10525v1)
| [PDF (v1)](https://arxiv.org/pdf/2609.10525v1)

The development proves the finite-witness characterization of generation in
the limit and the complete separation-width hierarchy. It includes the paper's
first-k normalization, its executable implementation on the natural numbers,
and the direct diagonal bounded-capture lemma.

## Source and credits

This is a focused derivative of
[generation-in-the-limit-lib](https://github.com/pengzhang91/generation-in-the-limit-lib),
developed and maintained by **Shuangping Li and Peng Zhang**, as credited in
the upstream README. The base revision is
[`de0d70c7e4645bface1d19bded9c8a5ade080fa8`](https://github.com/pengzhang91/generation-in-the-limit-lib/tree/de0d70c7e4645bface1d19bded9c8a5ade080fa8).
We retain its sequence-input model and required core files, and add the
`GenLimit.FiniteWitness` modules. The upstream Apache-2.0 license is preserved.
See [CREDITS.md](CREDITS.md) for the attribution and
[UPSTREAM.json](UPSTREAM.json) for file-level provenance.

This repository contains the source closure needed for this paper, rather than
the upstream library's full collection of unrelated formalizations.

## Build

Install [elan](https://github.com/leanprover/elan), then run from this repository:

```sh
cd GenLimitLean
lake exe cache get
lake build
```

`lean-toolchain` pins **Lean 4.24.0**. The committed `lake-manifest.json`
pins Mathlib to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` and records its
dependencies. The default build includes the aggregate audit, which prints
theorem signatures, axiom dependencies, and executable examples. To run that
target explicitly:

```sh
lake build GenLimit.FiniteWitness.Simplified.Audit
```

For use in another Lean file:

```lean
import GenLimit.FiniteWitness.Simplified
import GenLimit.FiniteWitness.Width
```

## What is checked

The model allows arbitrary, possibly uncountable families of infinite languages
over a countably infinite universe. Inputs are exhaustive positive texts with
repetitions. One total deterministic generator must eventually output a target
element absent from the observed input. Freshness does not compare against
previous generated outputs.

- Generation in the limit, set-driven generation, and compatible finite positive
  witness assignments are equivalent.
- One normalization is fixed before all targets on which the original generator
  succeeds; each such target has a finite locking witness.
- Positive separation gives exactly the same witness condition. Its width takes
  every value in `0, 1, 2, ..., omega, omega + 1`.
- Exact finite examples, the two-core omega example, chain divergence, endpoints,
  countable-support and finite-profile obstructions, and the appendix results
  have checked declarations.

[STATEMENT_MAP.md](docs/STATEMENT_MAP.md) gives the correspondence and its limits.
[CHECKING.md](docs/CHECKING.md) records the actual build and trusted components.

The new executable search is related to the mathematical normalization by
proved equalities and a locking theorem. There is no separate Mathlib
`Computable`/`Partrec` theorem or verified compiler-to-Turing-machine bridge.
The earlier implementation remains available; its `2|S|` query-word-length bound
belongs to that earlier implementation. No running-time or convergence-rate
bound is asserted for the current algorithm.

## Availability and citation

The paper is available on [arXiv](https://arxiv.org/abs/2609.10525), and this
[Lean development](https://github.com/xiaoyulics/language-generation-characterization)
is public. Please cite the paper when referring to its results:

```bibtex
@misc{li2026characterizinglanguagegeneration,
  title         = {Characterizing Language Generation in the Limit: Finite Witnesses and a Separation-Width Hierarchy},
  author        = {Xiaoyu Li and Andi Han and Jiaojiao Jiang and Junbin Gao},
  year          = {2026},
  eprint        = {2609.10525},
  archivePrefix = {arXiv},
  primaryClass  = {cs.FL},
  url           = {https://arxiv.org/abs/2609.10525}
}
```

Software citation metadata are in [CITATION.cff](CITATION.cff).

The code is distributed under [Apache-2.0](LICENSE). Third-party dependencies
retain their own licenses.
