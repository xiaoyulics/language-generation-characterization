# Credits and provenance

## Upstream library

This project builds on **generation-in-the-limit-lib**:

- Repository: https://github.com/pengzhang91/generation-in-the-limit-lib
- Base commit: `de0d70c7e4645bface1d19bded9c8a5ade080fa8`
- Developers and maintainers credited by the upstream README:
  **Shuangping Li** and **Peng Zhang**.
- License: **Apache License 2.0**. The complete upstream `LICENSE` is retained
  without modification.

The inherited files are `GenLimit/Core/Basic.lean`, `ClassGeneration.lean`,
`GenericGeneration.lean`, and `Text.lean`, under `GenLimitLean/`. They supply
the language, text, generator, correctness, and class-generation infrastructure.
Their bytes are unchanged from the base commit. The upstream Lean toolchain and
dependency lockfile are also retained unchanged.

The root `GenLimit.lean` import list and `lakefile.toml` are adapted to this
focused distribution. The rest of the upstream repository has not been copied.
`UPSTREAM.json` records source hashes and whether each included Lean/config file
is inherited, adapted, or added. The upstream README is the source of the
maintainer attribution above; this is an independent derivative repository.

## This manuscript and extension

The accompanying manuscript is by **Xiaoyu Li, Andi Han, Jiaojiao Jiang, and
Junbin Gao**. The `GenLimit/FiniteWitness.lean` entry point and
`GenLimit/FiniteWitness/` modules were added for this project. They cover the
finite-witness characterization, universal normalization, positive separation,
width hierarchy, obstructions, and supporting results.

The `Simplified` modules formalize the normalization and diagonal capture proof
used in the current manuscript. The earlier normalization remains in separate
modules. These additions are not attributed to the upstream maintainers.
Development and proof formalization in this project were assisted by OpenAI
Codex. Lean checking and the statement-correspondence assessment are documented
separately; neither is a claim about originality or publication readiness.

## Dependencies

The proofs use **Lean 4** and **Mathlib**, with all versions fixed by the
committed toolchain and dependency manifest. Credit also belongs to their
contributors. This repository's license does not replace dependency licenses.
